//! An implementation of DPLL that maintains a map between literals and clauses that contain it.
//!
//! - O(1) amortized find unit clause + O(#lits in clause) find the unit literal within
//! - O(#clauses with var) set variable
//! - O(#clauses with var) undo set variable
//! - O(#vars) find unset variable (an O(1) amortized implementation performed worse)
use super::*;

pub struct ClauseMappingState<TStats: StatsStorage> {
    variables: VariableStates,
    cnf: CNF,
    change_stack: Vec<ChangeStackItem>,
    literal_to_clause_map: LiteralToClauseMap,
    clauses: ClauseStates,
    stats: TStats,
}

enum ChangeStackItem {
    UnitPropagation,
    SetVariable {
        variable: Variable,
        previous_state: VariableState,
    },
    SetClauseState {
        clause_index: usize,
        previous_state: ClauseState,
    },
}

struct LiteralIncidences {
    clause_indices: Vec<usize>,
}

impl LiteralIncidences {
    pub fn new() -> Self {
        LiteralIncidences {
            clause_indices: Vec::new(),
        }
    }
}

/// This map allows finding clauses that contain a given literal.
struct LiteralToClauseMap {
    incidences: Vec<LiteralIncidences>,
}

impl LiteralToClauseMap {
    fn new(max_variable: Variable) -> Self {
        let mut incidences = Vec::new();
        for _ in 0..((max_variable.number() + 1) * 2) {
            incidences.push(LiteralIncidences::new());
        }
        Self { incidences }
    }

    fn from_cnf(cnf: &CNF, max_variable: Variable) -> Self {
        let mut map = Self::new(max_variable);

        for (i, clause) in cnf.clauses.iter().enumerate() {
            for &literal in &clause.literals {
                map.add_clause(literal, i)
            }
        }

        map
    }

    fn add_clause(&mut self, literal: Literal, clause_index: usize) {
        self.incidences[Self::literal_index(literal)]
            .clause_indices
            .push(clause_index);
    }

    #[inline]
    fn literal_index(literal: Literal) -> usize {
        let offset: usize = if literal.value() { 1 } else { 0 };
        literal.variable().number() as usize * 2 + offset
    }

    #[inline]
    fn clauses(&self, literal: Literal) -> &[usize] {
        &self.incidences[Self::literal_index(literal)].clause_indices
    }
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
enum ClauseState {
    Satisfied,
    Unsatisfied { unset_size: usize },
}

impl ClauseState {
    #[inline]
    fn is_satisfied(self) -> bool {
        self == ClauseState::Satisfied
    }

    #[inline]
    fn is_unit(self) -> bool {
        matches!(self, ClauseState::Unsatisfied { unset_size: 1 })
    }
}

struct ClauseStates {
    states_by_index: Vec<ClauseState>,
    unsatisfied: usize,
    /// Contains indices for all clauses that are unit, but may
    /// also contain clauses that are not unit anymore.
    unit_candidate_indices: Vec<usize>,
}

impl ClauseStates {
    fn from_cnf(cnf: &CNF) -> Self {
        let unit_clause_indices = cnf
            .clauses
            .iter()
            .enumerate()
            .filter(|(_, x)| x.is_unit())
            .map(|(i, _)| i);

        let mut states = ClauseStates {
            states_by_index: Vec::new(),
            unsatisfied: cnf.clauses.len(),
            unit_candidate_indices: unit_clause_indices.collect(),
        };

        for clause in &cnf.clauses {
            states.states_by_index.push(ClauseState::Unsatisfied {
                unset_size: clause.len(),
            });
        }

        states
    }

    fn get_unit_clause_index(&mut self) -> Option<usize> {
        // Unit clause candidates may also contain clauses that are not unit anymore.
        // We remove all the clauses from the end that are not unit anymore.
        while let Some(index) = self.unit_candidate_indices.last() {
            if self.is_unit(*index) {
                break;
            } else {
                self.unit_candidate_indices.pop();
            }
        }

        // We do not pop the found index clause as we want to maintain the invariant of all unit
        // clauses being included in `unit_candidate_indices` and it may stay unit after this
        // function is called.
        self.unit_candidate_indices.last().copied()
    }

    #[inline]
    fn is_unit(&self, clause_index: usize) -> bool {
        self.states_by_index[clause_index].is_unit()
    }

    #[inline]
    fn state(&self, clause_index: usize) -> ClauseState {
        self.states_by_index[clause_index]
    }

    fn set_state(&mut self, clause_index: usize, new_state: ClauseState) {
        let old_state = &mut self.states_by_index[clause_index];
        if !old_state.is_satisfied() && new_state.is_satisfied() {
            self.unsatisfied -= 1;
        } else if old_state.is_satisfied() && !new_state.is_satisfied() {
            self.unsatisfied += 1;
        }

        if new_state.is_unit() {
            self.unit_candidate_indices.push(clause_index);
        }

        *old_state = new_state;
    }
}

impl<TStats: StatsStorage> DpllState<TStats> for ClauseMappingState<TStats> {
    fn new(cnf: CNF, max_variable: Variable) -> Self {
        ClauseMappingState {
            variables: VariableStates::new_unset(max_variable),
            literal_to_clause_map: LiteralToClauseMap::from_cnf(&cnf, max_variable),
            clauses: ClauseStates::from_cnf(&cnf),
            cnf,
            change_stack: Vec::new(),
            stats: Default::default(),
        }
    }

    #[inline]
    fn start_unit_propagation(&mut self) {
        self.change_stack.push(ChangeStackItem::UnitPropagation);
    }

    fn undo_last_unit_propagation(&mut self) {
        loop {
            match self.change_stack.pop() {
                Some(ChangeStackItem::UnitPropagation) => {
                    break;
                }
                Some(ChangeStackItem::SetClauseState {
                    clause_index,
                    previous_state,
                }) => {
                    self.clauses.set_state(clause_index, previous_state);
                }
                Some(ChangeStackItem::SetVariable {
                    variable,
                    previous_state,
                }) => self.undo_variable_set_inner(variable, previous_state),
                None => unreachable!("Undoing a unit propagation that did not happen"),
            }
        }
    }

    #[inline]
    fn all_clauses_satisfied(&self) -> bool {
        self.clauses.unsatisfied == 0
    }

    #[inline]
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

    #[inline]
    fn stats(&mut self) -> &mut TStats {
        &mut self.stats
    }

    #[inline]
    fn set_variable_to_literal(&mut self, literal: Literal) -> SetVariableOutcome {
        self.set_variable(literal.variable(), literal.value().into())
    }

    fn set_variable(&mut self, variable: Variable, state: VariableState) -> SetVariableOutcome {
        let variable_state = self.variables.get(variable);

        self.change_stack.push(ChangeStackItem::SetVariable {
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

            // A clause that contains both a literal and its negation would get
            // processed twice. These clauses can and should be ignored.
            debug_assert!(!self
                .literal_to_clause_map
                .clauses(new_literal)
                .iter()
                .any(|x| self.literal_to_clause_map.clauses(!new_literal).contains(x)));

            // All clauses that contain this literal are now satisfied.
            for &clause in self.literal_to_clause_map.clauses(new_literal) {
                self.stats.increment_clause_state_updates();
                self.change_stack.push(ChangeStackItem::SetClauseState {
                    clause_index: clause,
                    previous_state: self.clauses.state(clause),
                });
                self.clauses.set_state(clause, ClauseState::Satisfied);
            }

            // All clauses that contain the negated literal have
            // it removed; moving towards unsatisfiability
            for &clause in self.literal_to_clause_map.clauses(!new_literal) {
                self.stats.increment_clause_state_updates();
                let old_state = self.clauses.state(clause);
                if let ClauseState::Unsatisfied { unset_size: size } = old_state {
                    // We assume the literal only occurs once in the clause.
                    let new_size = size - 1usize;

                    self.change_stack.push(ChangeStackItem::SetClauseState {
                        clause_index: clause,
                        previous_state: old_state,
                    });
                    self.clauses.set_state(
                        clause,
                        ClauseState::Unsatisfied {
                            unset_size: new_size,
                        },
                    );

                    if new_size == 0 {
                        return SetVariableOutcome::Unsatisfiable;
                    }
                }
            }
        }

        SetVariableOutcome::Ok
    }

    fn undo_last_set_variable(&mut self) {
        loop {
            match self.change_stack.pop() {
                Some(ChangeStackItem::SetClauseState {
                    clause_index,
                    previous_state,
                }) => {
                    self.stats.increment_clause_state_updates();
                    self.clauses.set_state(clause_index, previous_state);
                }
                Some(ChangeStackItem::SetVariable {
                    variable,
                    previous_state,
                }) => {
                    self.undo_variable_set_inner(variable, previous_state);
                    break;
                }
                None => panic!("Undoing a variable that has not been set"),
                Some(ChangeStackItem::UnitPropagation) => {
                    panic!("Undoing across a unit propagation boundary")
                }
            }
        }
    }

    #[inline]
    fn next_unit_literal(&mut self) -> Option<Literal> {
        let unit_index = self.clauses.get_unit_clause_index();
        unit_index.and_then(|index| {
            self.cnf.clauses[index]
                .literals
                .iter()
                .find(|lit| self.variables.is_unset(lit.variable()))
                .cloned()
        })
    }
}

impl<TStats: StatsStorage> ClauseMappingState<TStats> {
    fn undo_variable_set_inner(&mut self, variable: Variable, previous_state: VariableState) {
        let state = self.variables.get(variable);
        self.variables.set(variable, previous_state);

        if state != VariableState::Unset {
            let new_literal = Literal::new(
                variable,
                match state {
                    VariableState::True => true,
                    VariableState::False => false,
                    VariableState::Unset => unreachable!(),
                },
            );

            // A clause that contains both a literal and its negation would get
            // processed twice. These clauses can and should be ignored.
            debug_assert!(!self
                .literal_to_clause_map
                .clauses(new_literal)
                .iter()
                .any(|x| self.literal_to_clause_map.clauses(!new_literal).contains(x)));
        }
    }
}
