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

struct State<TStats: StatsStorage> {
    variables: Vec<VariableState>,
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

pub fn solve<TStatistics: StatsStorage>(cnf: &CNF) -> (Solution, TStatistics) {
    let max_variable = match cnf
        .clauses
        .iter()
        .flat_map(|x| x.literals.iter().map(|x| x.variable()))
        .max()
    {
        Some(max) => max,
        None => {
            // CNF with no variables
            return if cnf.clauses.is_empty() {
                (Solution::Satisfiable(Vec::new()), Default::default())
            } else {
                // There is an empty clause, which is unsatisfiable.
                (Solution::Unsatisfiable, Default::default())
            };
        }
    };

    let mut state = State::<TStatistics>::new(max_variable, cnf.clone());
    match cnf_transforming::dpll(&mut state) {
        BranchOutcome::Satisfiable(variables) => (Solution::Satisfiable(variables), state.stats),
        BranchOutcome::Unsatisfiable => (Solution::Unsatisfiable, state.stats),
    }
}

fn dpll<TStats: StatsStorage>(state: &mut State<TStats>) -> BranchOutcome {
    let propagation_result = unit_propagation(state);

    if propagation_result == UnitPropagationOutcome::Unsatisfiable {
        state.undo_last_unit_propagation();
        return BranchOutcome::Unsatisfiable;
    }

    if state.cnf.is_satisfied() {
        return BranchOutcome::Satisfiable(state.variables.clone());
    }
    if state.cnf.is_unsatisfiable() {
        state.undo_last_unit_propagation();
        return BranchOutcome::Unsatisfiable;
    }

    // The unsatisfiability check above should ensure there is an unset variable.
    let next_variable = state.first_unset_variable().unwrap();

    for variable_state in [VariableState::True, VariableState::False] {
        state.stats.increment_decisions();

        if state.set_variable(next_variable, variable_state) == SetVariableOutcome::Ok {
            let outcome = dpll(state);
            if outcome.is_satisfiable() {
                return outcome;
            }
        }
        state.undo_last_set_variable();
    }

    state.undo_last_unit_propagation();

    BranchOutcome::Unsatisfiable
}

#[must_use]
#[derive(Eq, PartialEq, Debug)]
enum UnitPropagationOutcome {
    Finished,
    Unsatisfiable,
}

fn unit_propagation<TStats: StatsStorage>(state: &mut State<TStats>) -> UnitPropagationOutcome {
    state.cnf_change_stack.push(CNFStackItem::UnitPropagation);

    loop {
        let unit_literal = state
            .cnf
            .clauses
            .iter()
            .find(|clause| clause.literals.len() == 1)
            .map(|clause| clause.literals[0]);

        if let Some(literal) = unit_literal {
            debug_assert!(*state.variable_state(literal.variable()) == VariableState::Unset);

            state.stats.increment_unit_propagation_steps();

            if let SetVariableOutcome::Unsatisfiable =
                state.set_variable(literal.variable(), literal.value().into())
            {
                return UnitPropagationOutcome::Unsatisfiable;
            }
        } else {
            break;
        }
    }

    UnitPropagationOutcome::Finished
}

#[must_use]
#[derive(Eq, PartialEq, Debug)]
enum SetVariableOutcome {
    Ok,
    Unsatisfiable,
}

impl<TStatistics: StatsStorage> State<TStatistics> {
    fn new(max_variable: Variable, cnf: CNF) -> Self {
        State {
            // We allocate one extra element to make indexing trivial.
            variables: vec![VariableState::Unset; (max_variable.number() + 1) as usize],
            cnf,
            cnf_change_stack: Vec::new(),
            stats: Default::default(),
        }
    }

    fn first_unset_variable(&self) -> Option<Variable> {
        self.variables
            .iter()
            .enumerate()
            .skip(1)
            .find(|(_, &x)| x == VariableState::Unset)
            .map(|(i, _)| Variable::new(i as VariableType))
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
                    self.variables[variable.number() as usize] = previous_state;
                }
                None => panic!("Undoing a unit propagation that did not happen"),
            }
        }
    }

    fn undo_last_set_variable(&mut self) {
        loop {
            match self.cnf_change_stack.pop() {
                Some(CNFStackItem::Change(change)) => change.undo(&mut self.cnf),
                Some(CNFStackItem::SetVariable {
                    variable,
                    previous_state,
                }) => {
                    self.variables[variable.number() as usize] = previous_state;
                    break;
                }
                None => panic!("Undoing a variable that has not been set"),
                Some(CNFStackItem::UnitPropagation) => {
                    panic!("Undoing across a unit propagation boundary")
                }
            }
        }
    }

    fn variable_state(&self, variable: Variable) -> &VariableState {
        &self.variables[variable.number() as usize]
    }

    fn set_variable(&mut self, variable: Variable, state: VariableState) -> SetVariableOutcome {
        let variable_state = &mut self.variables[variable.number() as usize];

        self.cnf_change_stack.push(CNFStackItem::SetVariable {
            variable,
            previous_state: *variable_state,
        });
        *variable_state = state;

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
                        if clause.literals.len() == 1 {
                            // If the clause becomes empty, we report it.
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn three_variables_sat() {
        let mut cnf = CNF::new();

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        clause.add_variable(Variable::new(2), true);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(2), false);
        clause.add_variable(Variable::new(3), false);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(3), true);
        clause.add_variable(Variable::new(4), false);
        cnf.add_clause(clause);

        assert!(matches!(solve::<NoStats>(&cnf).0, Solution::Satisfiable(_)));
    }

    #[test]
    fn three_variables_unit_propagation_sat() {
        let mut cnf = CNF::new();

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), true);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        clause.add_variable(Variable::new(2), true);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(2), false);
        clause.add_variable(Variable::new(3), true);
        cnf.add_clause(clause);

        assert!(matches!(solve::<NoStats>(&cnf).0, Solution::Satisfiable(_)));
    }

    #[test]
    fn empty_sat() {
        let cnf = CNF::new();

        assert!(matches!(solve::<NoStats>(&cnf).0, Solution::Satisfiable(_)));
    }

    #[test]
    fn empty_clause_unsat() {
        let mut cnf = CNF::new();
        let clause = Clause::new();
        cnf.add_clause(clause);

        assert!(matches!(solve::<NoStats>(&cnf).0, Solution::Unsatisfiable));
    }

    #[test]
    fn two_conflicting_clause_unsat() {
        let mut cnf = CNF::new();

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), true);
        cnf.add_clause(clause);

        assert!(matches!(solve::<NoStats>(&cnf).0, Solution::Unsatisfiable));
    }
}
