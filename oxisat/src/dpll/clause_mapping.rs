//! An implementation of DPLL that maintains a map between literals and clauses that contain it.
//!
//! TODO: Finish docs after this is implemented.
//! - O(?) unit propagation search
//! - O(?) set variable
//! - O(?) unset variable
//! - O(?) removing/restoring a clause
//! - O(?) removing/restoring a literal
//!
use super::*;

struct State<TStats: StatsStorage> {
    variables: Vec<VariableState>,
    cnf: CNF,
    cnf_change_stack: Vec<CNFStackItem>,
    literal_to_clause_map: LiteralToClauseMap,
    clauses: ClauseStates,
    stats: TStats,
}

enum CNFStackItem {
    UnitPropagation,
    SetVariable {
        variable: Variable,
        previous_state: VariableState,
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

    fn clauses(&self, literal: Literal) -> &Vec<usize> {
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
                unset_size: clause.literals.len(),
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

    fn get_state(&self, clause_index: usize) -> &ClauseState {
        &self.states_by_index[clause_index]
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

pub fn solve<TStatistics: StatsStorage>(cnf: &CNF) -> (Solution, TStatistics) {
    let max_variable = match cnf.max_variable() {
        Some(max) => max,
        None => {
            return if cnf.clauses.is_empty() {
                // CNF with no variables
                (Solution::Satisfiable(Vec::new()), Default::default())
            } else {
                // There is an empty clause, which is unsatisfiable.
                (Solution::Unsatisfiable, Default::default())
            };
        }
    };

    let mut state = State::<TStatistics>::new(max_variable, cnf.clone());
    match dpll(&mut state) {
        BranchOutcome::Satisfiable(variables) => (Solution::Satisfiable(variables), state.stats),
        BranchOutcome::Unsatisfiable => (Solution::Unsatisfiable, state.stats),
    }
}

fn dpll<TStats: StatsStorage>(state: &mut State<TStats>) -> BranchOutcome {
    debug_assert!(state.verify_consistency());
    let propagation_result = unit_propagation(state);

    if propagation_result == UnitPropagationOutcome::Unsatisfiable {
        state.undo_last_unit_propagation();
        return BranchOutcome::Unsatisfiable;
    }

    if state.clauses.unsatisfied == 0 {
        return BranchOutcome::Satisfiable(state.variables.clone());
    }

    // The unsatisfiability check at the unit propagation result
    // should ensure there is an unset variable.
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
        let unit_index = state.clauses.get_unit_clause_index();
        let unit_literal = unit_index.and_then(|index| {
            state.cnf.clauses[index]
                .literals
                .iter()
                .find(|lit| *state.variable_state(lit.variable()) == VariableState::Unset)
                .cloned()
        });

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
            literal_to_clause_map: LiteralToClauseMap::from_cnf(&cnf, max_variable),
            clauses: ClauseStates::from_cnf(&cnf),
            cnf,
            cnf_change_stack: Vec::new(),
            stats: Default::default(),
        }
    }

    fn variable_state(&self, variable: Variable) -> &VariableState {
        &self.variables[variable.number() as usize]
    }

    fn first_unset_variable(&self) -> Option<Variable> {
        // TODO: Maintain a set of unset variables (?)
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
                Some(CNFStackItem::SetVariable {
                    variable,
                    previous_state,
                }) => self.undo_variable_set_inner(variable, previous_state),
                None => unreachable!("Undoing a unit propagation that did not happen"),
            }
        }
    }

    fn calculate_clause_state(&self, clause_index: usize) -> ClauseState {
        let clause = &self.cnf.clauses[clause_index];
        let mut unsatisfied = 0;
        for &lit in &clause.literals {
            let state = self.variable_state(lit.variable());

            if state.satisfies(lit) {
                // If any literal is satisfied, the entire clause is.
                return ClauseState::Satisfied;
            }

            if state.unsatisfies(lit) {
                // If the variable is set to the opposite value, it is unsatisfied.
                unsatisfied += 1;
            } else {
                // The value is unset.
            }
        }

        let clause_size = clause.literals.len();
        ClauseState::Unsatisfied {
            unset_size: clause_size - unsatisfied,
        }
    }

    fn undo_last_set_variable(&mut self) {
        loop {
            match self.cnf_change_stack.pop() {
                Some(CNFStackItem::SetVariable {
                    variable,
                    previous_state,
                }) => {
                    self.undo_variable_set_inner(variable, previous_state);
                    break;
                }
                None => panic!("Undoing a variable that has not been set"),
                Some(CNFStackItem::UnitPropagation) => {
                    panic!("Undoing across a unit propagation boundary")
                }
            }
        }
    }

    fn undo_variable_set_inner(&mut self, variable: Variable, previous_state: VariableState) {
        let state = self.variables[variable.number() as usize];
        self.variables[variable.number() as usize] = previous_state;
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

            // All clauses that contain this literal were satisfied and need to be
            // rescanned as they might still be satisfied from another literal.
            for clause in self.literal_to_clause_map.clauses(new_literal) {
                self.clauses
                    .set_state(*clause, self.calculate_clause_state(*clause));
            }

            // All clauses that contain the negated literal have it added back
            for clause in self.literal_to_clause_map.clauses(!new_literal) {
                self.clauses
                    .set_state(*clause, self.calculate_clause_state(*clause));
            }
        }
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

            // A clause that contains both a literal and its negation would get
            // processed twice. These clauses can and should be ignored.
            debug_assert!(!self
                .literal_to_clause_map
                .clauses(new_literal)
                .iter()
                .any(|x| self.literal_to_clause_map.clauses(!new_literal).contains(x)));

            // All clauses that contain this literal are now satisfied.
            for clause in self.literal_to_clause_map.clauses(new_literal) {
                self.clauses.set_state(*clause, ClauseState::Satisfied);
            }

            // All clauses that contain the negated literal have
            // it removed; moving towards unsatisfiability
            for clause in self.literal_to_clause_map.clauses(!new_literal) {
                let old_state = self.clauses.get_state(*clause);
                if let ClauseState::Unsatisfied { unset_size: size } = old_state {
                    // We assume the literal only occurs once in the clause.
                    let new_size = *size - 1usize;

                    self.clauses.set_state(
                        *clause,
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

    fn verify_consistency(&self) -> bool {
        for i in 0..self.cnf.clauses.len() {
            let real_state = self.calculate_clause_state(i);
            if *self.clauses.get_state(i) != real_state {
                debug_assert!(false);
                return false;
            }
        }

        true
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
