//! An implementation of DPLL that maintains a CNF that is transformed with each decision.
//!
//! This transformed CNF has fewer and fewer clauses and literals as the search gets deeper.
//! However, it is highly unlikely this implementation is any better than alternatives.
//! The transformed CNF does not necessarily keep the same order of clauses and literals.
//!
//! The current implementation can be expanded by adding a new array that maps
//! clause_index -> current_clause_index, and by adding the clause index to clauses to implement
//! the reverse mapping. This map can be maintained in O(1) time for each operation and would allow
//! implementing optimizations that require references to clauses.
//!
//! - O(clauses + literals) unit propagation search
//! - O(clauses + literals) set variable
//!   ^ note that these apply to the transformed CNF, which often
//!     has fewer clauses or literals than the original.
//! - O(#changes)           unset variable
//! - O(1)                  removing/restoring a clause
//! - O(1)                  removing/restoring a literal
//!
//! CNF changes do not require allocations, but the stack storing a list of changes
//! may need them when initially expanding.
use super::*;

pub struct CnfTransformingState<TStats: StatsStorage> {
    variables: VariableStates,
    cnf: CNF,
    cnf_change_stack: Vec<CNFStackItem>,
    stats: TStats,
}

enum CNFStackItem {
    UnitPropagation,
    SetVariable {
        variable: Variable,
        previous_state: VariableState,
    },
    Change(CNFChange),
}

enum CNFChange {
    RemoveClause {
        clause: Clause,
        clause_index: usize,
    },
    RemoveLiteral {
        literal: Literal,
        clause_index: usize,
    },
}

impl CNFChange {
    fn undo(self, cnf: &mut CNF) {
        match self {
            CNFChange::RemoveClause {
                clause,
                clause_index,
            } => {
                let len = cnf.clauses.len();
                cnf.clauses.push(clause);
                // We used `swap_remove` to remove the clause, we need to invert this operation
                // to maintain index validity within other changes.
                cnf.clauses.swap(clause_index, len);
            }
            CNFChange::RemoveLiteral {
                literal,
                clause_index,
            } => cnf.clauses[clause_index].literals.push(literal),
        }
    }
}

impl<TStats: StatsStorage> DpllState<TStats> for CnfTransformingState<TStats> {
    fn new(cnf: CNF, max_variable: Variable) -> Self {
        CnfTransformingState {
            variables: VariableStates::new_unset(max_variable),
            cnf,
            cnf_change_stack: Vec::new(),
            stats: Default::default(),
        }
    }

    fn start_unit_propagation(&mut self) {
        self.cnf_change_stack.push(CNFStackItem::UnitPropagation);
    }

    fn undo_last_unit_propagation(&mut self) {
        loop {
            match self.cnf_change_stack.pop() {
                Some(CNFStackItem::UnitPropagation) => {
                    break;
                }
                Some(CNFStackItem::Change(change)) => change.undo(&mut self.cnf),
                Some(CNFStackItem::SetVariable {
                    variable,
                    previous_state,
                }) => {
                    self.variables.set(variable, previous_state);
                }
                None => panic!("Undoing a unit propagation that did not happen"),
            }
        }
    }

    fn all_clauses_satisfied(&self) -> bool {
        self.cnf.is_satisfied()
    }

    fn next_unset_variable(&self) -> Option<Variable> {
        // We choose the variable with the lowest index.
        self.variables
            .iter()
            .enumerate()
            .skip(1)
            .find(|(_, &x)| x == VariableState::Unset)
            .map(|(i, _)| Variable::new(i as VariableType))
    }

    fn into_result(self) -> (Solution, TStats) {
        if self.all_clauses_satisfied() {
            (Solution::Satisfiable(self.variables), self.stats)
        } else {
            (Solution::Unsatisfiable, self.stats)
        }
    }

    fn stats(&mut self) -> &mut TStats {
        &mut self.stats
    }

    fn set_variable_to_literal(&mut self, literal: Literal) -> SetVariableOutcome {
        self.set_variable(literal.variable(), literal.value().into())
    }

    fn set_variable(&mut self, variable: Variable, state: VariableState) -> SetVariableOutcome {
        let variable_state = self.variables.get(variable);

        self.cnf_change_stack.push(CNFStackItem::SetVariable {
            variable,
            previous_state: variable_state,
        });
        self.variables.set(variable, state);

        if state != VariableState::Unset {
            let new_literal = Literal::new(
                variable,
                match state {
                    VariableState::True => true,
                    VariableState::False => false,
                    VariableState::Unset => unreachable!(),
                },
            );

            let new_literal_negated = !new_literal;

            // We need to manually maintain the current clause index and the maximum as we will
            // be modifying the clause Vec while iterating through it.
            let mut clause_i = 0;
            let mut max_clause_i = self.cnf.clauses.len();

            while clause_i < max_clause_i {
                enum LiteralSearchResult {
                    None,
                    Found,
                    FoundNegated(usize),
                }

                let mut search_result = LiteralSearchResult::None;

                for (i, &literal) in self.cnf.clauses[clause_i].literals.iter().enumerate() {
                    if literal == new_literal {
                        search_result = LiteralSearchResult::Found;
                        break;
                    }
                    if literal == new_literal_negated {
                        search_result = LiteralSearchResult::FoundNegated(i);
                        // We assume there are no variable duplicates within one clause.
                        break;
                    }
                }

                match search_result {
                    LiteralSearchResult::Found => {
                        // The clause is satisfied; the entire clause is removed.
                        let removed_clause = self.cnf.clauses.swap_remove(clause_i);
                        self.cnf_change_stack
                            .push(CNFStackItem::Change(CNFChange::RemoveClause {
                                clause: removed_clause,
                                clause_index: clause_i,
                            }));

                        max_clause_i -= 1;
                        // `clause_i` is not incremented as we need to check the clause
                        // that used to be last.
                    }
                    LiteralSearchResult::FoundNegated(literal_index) => {
                        // Negation found; only this single literal is removed.
                        let clause = &mut self.cnf.clauses[clause_i];
                        if clause.is_unit() {
                            // The clause would become empty, we report it as unsatisfiable.
                            return SetVariableOutcome::Unsatisfiable;
                        }
                        clause.literals.swap_remove(literal_index);
                        self.cnf_change_stack.push(CNFStackItem::Change(
                            CNFChange::RemoveLiteral {
                                literal: new_literal_negated,
                                clause_index: clause_i,
                            },
                        ));
                        clause_i += 1;
                    }
                    LiteralSearchResult::None => {
                        clause_i += 1;
                    }
                }
            }
        }

        SetVariableOutcome::Ok
    }

    fn undo_last_set_variable(&mut self) {
        loop {
            match self.cnf_change_stack.pop() {
                Some(CNFStackItem::Change(change)) => change.undo(&mut self.cnf),
                Some(CNFStackItem::SetVariable {
                    variable,
                    previous_state,
                }) => {
                    self.variables.set(variable, previous_state);
                    break;
                }
                None => panic!("Undoing a variable that has not been set"),
                Some(CNFStackItem::UnitPropagation) => {
                    panic!("Undoing across a unit propagation boundary")
                }
            }
        }
    }

    fn next_unit_literal(&mut self) -> Option<Literal> {
        self.cnf
            .clauses
            .iter()
            .find(|clause| clause.is_unit())
            .map(|clause| clause.literals[0])
    }
}
