mod clause_mapping;
mod cnf_transforming;
mod preprocessing;
mod watched_literals;

#[cfg(test)]
mod tests;

use crate::dimacs;
use crate::dimacs::Dimacs;
use crate::dpll::clause_mapping::ClauseMappingState;
use crate::dpll::cnf_transforming::CnfTransformingState;
use crate::dpll::watched_literals::WatchedState;
use crate::dpll::preprocessing::PreprocessingResult;

/// The underlying type that is used to handle variables.
/// This is a signed integer type.
type VariableType = i32;

pub const MAX_VARIABLE_COUNT: usize = (VariableType::MAX - 1) as usize;

/// Represents a boolean variable without a value.
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct Variable(VariableType);

/// Represents a literal, i.e. a variable with a set value (true or false).
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Literal(VariableType);

/// Represents a CNF clause (a disjunction of literals).
#[derive(Clone, Debug)]
pub struct Clause {
    literals: Vec<Literal>,
}

/// Represents a formula in a Conjunctive normal form (a conjunction of disjunction clauses).
#[derive(Clone, Debug)]
pub struct CNF {
    clauses: Vec<Clause>,
}

impl From<Dimacs> for CNF {
    fn from(dimacs: Dimacs) -> Self {
        let mut cnf = CNF::new();

        for dimacs_clause in dimacs.clauses() {
            let mut clause = Clause::new();

            for literal in dimacs_clause.literals() {
                clause.add_literal(match literal {
                    dimacs::Literal::Positive(variable) => Literal::new(
                        Variable((*variable).try_into().expect(
                            "Variable index does not fit into the range of the underlying type",
                        )),
                        true,
                    ),
                    dimacs::Literal::Negative(variable) => Literal::new(
                        Variable((*variable).try_into().expect(
                            "Variable index does not fit into the range of the underlying type",
                        )),
                        false,
                    ),
                });
            }

            cnf.add_clause(clause);
        }

        cnf
    }
}

impl Variable {
    /// Creates a new variable with a given **positive** number.
    ///
    /// # Panics
    /// Panics if `number <= 0` with a debug assert.
    /// The value is not checked when debug asserts are disabled.
    pub fn new(number: VariableType) -> Self {
        // For performance reasons, we only check this in debug mode.
        debug_assert!(number > 0);
        Variable(number)
    }

    #[inline]
    pub fn number(&self) -> VariableType {
        self.0
    }
}

impl Literal {
    /// Creates a new literal for a variable with a set value.
    pub fn new(variable: Variable, is_true: bool) -> Self {
        if is_true {
            Literal(variable.0)
        } else {
            Literal(-variable.0)
        }
    }

    /// Returns `true` if the literal is true.
    #[inline]
    fn value(self) -> bool {
        self.0 > 0
    }

    /// Returns the variable of the literal.
    #[inline]
    fn variable(self) -> Variable {
        if self.0 > 0 {
            Variable(self.0)
        } else {
            Variable(-self.0)
        }
    }

    #[inline]
    fn negated(self) -> Literal {
        Literal(-self.0)
    }
}

impl std::ops::Not for Literal {
    type Output = Literal;

    #[inline]
    fn not(self) -> Self::Output {
        self.negated()
    }
}

impl Clause {
    /// Creates a new empty clause.
    pub fn new() -> Self {
        Self {
            literals: Vec::new(),
        }
    }

    /// Adds a literal to the clause.
    pub fn add_literal(&mut self, literal: Literal) {
        self.literals.push(literal)
    }

    /// Adds a literal to the clause.
    pub fn add_variable(&mut self, variable: Variable, value: bool) {
        self.literals.push(Literal::new(variable, value))
    }

    #[inline]
    fn is_unit(&self) -> bool {
        self.len() == 1
    }

    #[inline]
    fn len(&self) -> usize {
        self.literals.len()
    }
}

impl CNF {
    /// Creates a new CNF with zero clauses.
    /// An empty CNF is considered to be satisfied.
    pub fn new() -> Self {
        CNF {
            clauses: Vec::new(),
        }
    }

    /// Adds a clause to the CNF.
    pub fn add_clause(&mut self, clause: Clause) {
        self.clauses.push(clause)
    }

    /// Returns `true` if this CNF is satisfied (i.e. contains no clauses).
    fn is_satisfied(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Returns the maximum variable used within the CNF.
    ///
    /// Runs in O(literals) time.
    fn max_variable(&self) -> Option<Variable> {
        self.clauses
            .iter()
            .flat_map(|x| x.literals.iter().map(|x| x.variable()))
            .max()
    }
}

pub enum Solution {
    Satisfiable(VariableStates),
    Unsatisfiable,
}

pub enum Implementation {
    Default,
    CnfTransforming,
    ClauseMapping,
    WatchedLiterals,
}

pub fn solve<TStatistics: StatsStorage>(
    cnf: &CNF,
    implementation: Implementation,
) -> (Solution, TStatistics) {
    match implementation {
        Implementation::Default => solve_cnf::<WatchedState<TStatistics>, TStatistics>(cnf),
        Implementation::CnfTransforming => {
            solve_cnf::<CnfTransformingState<TStatistics>, TStatistics>(cnf)
        }
        Implementation::ClauseMapping => {
            solve_cnf::<ClauseMappingState<TStatistics>, TStatistics>(cnf)
        }
        Implementation::WatchedLiterals => solve_cnf::<WatchedState<TStatistics>, TStatistics>(cnf)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum VariableState {
    False = 0,
    True = 1,
    Unset,
}

impl VariableState {
    #[inline]
    pub fn satisfies(&self, literal: Literal) -> bool {
        let literal_state: VariableState = literal.value().into();
        *self == literal_state
    }

    #[inline]
    pub fn unsatisfies(&self, literal: Literal) -> bool {
        let literal_state_negated: VariableState = (!literal.value()).into();
        *self == literal_state_negated
    }
}

#[derive(Clone)]
pub struct VariableStates(Vec<VariableState>);

impl VariableStates {
    fn new_unset(max_variable: Variable) -> Self {
        // We allocate one extra element to make indexing trivial.
        VariableStates(vec![
            VariableState::Unset;
            (max_variable.number() + 1) as usize
        ])
    }

    fn empty() -> Self {
        VariableStates(Vec::new())
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &VariableState> {
        self.0.iter()
    }

    #[inline]
    pub fn satisfies(&self, literal: Literal) -> bool {
        self.get(literal.variable()).satisfies(literal)
    }

    #[inline]
    pub fn unsatisfies(&self, literal: Literal) -> bool {
        self.get(literal.variable()).unsatisfies(literal)
    }

    #[inline]
    pub fn is_unset(&self, variable: Variable) -> bool {
        self.get(variable) == VariableState::Unset
    }

    #[inline]
    pub fn get(&self, variable: Variable) -> VariableState {
        self.0[variable.number() as usize]
    }

    #[inline]
    fn set(&mut self, variable: Variable, new_state: VariableState) {
        self.0[variable.number() as usize] = new_state
    }

    #[inline]
    fn set_to_literal(&mut self, literal: Literal) {
        self.set(literal.variable(), literal.value().into())
    }
}

impl From<bool> for VariableState {
    #[inline]
    fn from(value: bool) -> Self {
        if value {
            VariableState::True
        } else {
            VariableState::False
        }
    }
}

pub trait StatsStorage: Default {
    fn increment_decisions(&mut self);
    fn increment_unit_propagation_steps(&mut self);
    fn increment_clause_state_updates(&mut self);
}

#[derive(Default)]
pub struct NoStats;

#[derive(Default)]
pub struct Stats {
    decisions: u64,
    unit_propagation_steps: u64,
    clause_state_updates: u64,
}

impl Stats {
    pub fn decisions(&self) -> u64 {
        self.decisions
    }

    pub fn unit_propagation_steps(&self) -> u64 {
        self.unit_propagation_steps
    }

    pub fn clause_state_updates(&self) -> u64 {
        self.clause_state_updates
    }
}

impl StatsStorage for NoStats {
    #[inline(always)]
    fn increment_decisions(&mut self) {}
    #[inline(always)]
    fn increment_unit_propagation_steps(&mut self) {}
    #[inline(always)]
    fn increment_clause_state_updates(&mut self) {}
}

impl StatsStorage for Stats {
    #[inline]
    fn increment_decisions(&mut self) {
        self.decisions += 1;
    }

    #[inline]
    fn increment_unit_propagation_steps(&mut self) {
        self.unit_propagation_steps += 1;
    }

    #[inline]
    fn increment_clause_state_updates(&mut self) {
        self.clause_state_updates += 1;
    }
}

trait DpllState<TStats: StatsStorage> {
    fn new(cnf: CNF, max_variable: Variable) -> Self;
    fn start_unit_propagation(&mut self);
    fn undo_last_unit_propagation(&mut self);
    fn all_clauses_satisfied(&self) -> bool;
    fn next_unset_variable(&self) -> Option<Variable>;
    fn into_result(self) -> (Solution, TStats);
    fn stats(&mut self) -> &mut TStats;
    fn set_variable_to_literal(&mut self, literal: Literal) -> SetVariableOutcome;
    fn set_variable(&mut self, variable: Variable, state: VariableState) -> SetVariableOutcome;
    fn undo_last_set_variable(&mut self);
    fn next_unit_literal(&mut self) -> Option<Literal>;
}

#[must_use]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum DpllDecisionOutcome {
    Satisfiable,
    Unsatisfiable,
}

#[must_use]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum SetVariableOutcome {
    Ok,
    Unsatisfiable,
}

fn solve_cnf_without_variables<TStats: StatsStorage>(cnf: &CNF) -> (Solution, TStats) {
    if cnf.clauses.is_empty() {
        // CNF with no variables
        (
            Solution::Satisfiable(VariableStates::empty()),
            Default::default(),
        )
    } else {
        // There is an empty clause, which is unsatisfiable.
        (Solution::Unsatisfiable, Default::default())
    }
}

fn solve_cnf<TState: DpllState<TStats>, TStats: StatsStorage>(cnf: &CNF) -> (Solution, TStats) {
    let max_variable = match cnf.max_variable() {
        Some(max) => max,
        None => return solve_cnf_without_variables(cnf),
    };

    let mut cnf = cnf.clone();
    let preprocess_result = preprocessing::preprocess_cnf(&mut cnf, max_variable);

    match preprocess_result {
        PreprocessingResult::Unsatisfiable => (Solution::Unsatisfiable, Default::default()),
        PreprocessingResult::Preprocessed {
            new_max_variable, ..
        } => {
            let (solution, stats) = if let Some(max_variable) = new_max_variable {
                let mut state = TState::new(cnf, max_variable);

                let _ = dpll(&mut state);
                state.into_result()
            } else {
                solve_cnf_without_variables(&cnf)
            };

            // Map from processed variable space to the pre-processing space.
            (preprocess_result.reverse_map_solution(&solution), stats)
        }
    }
}

fn dpll<TState: DpllState<TStatistics>, TStatistics: StatsStorage>(
    state: &mut TState,
) -> DpllDecisionOutcome {
    let propagation_result = unit_propagation(state);

    if propagation_result == UnitPropagationOutcome::Unsatisfiable {
        state.undo_last_unit_propagation();
        return DpllDecisionOutcome::Unsatisfiable;
    }

    if state.all_clauses_satisfied() {
        return DpllDecisionOutcome::Satisfiable;
    }

    // The unsatisfiability check at the unit propagation result
    // should ensure there is an unset variable.
    let next_variable = state.next_unset_variable().unwrap();

    for variable_state in [VariableState::True, VariableState::False] {
        state.stats().increment_decisions();

        if state.set_variable(next_variable, variable_state) == SetVariableOutcome::Ok {
            let outcome = dpll(state);
            if outcome == DpllDecisionOutcome::Satisfiable {
                return outcome;
            }
        }
        state.undo_last_set_variable();
    }

    state.undo_last_unit_propagation();

    DpllDecisionOutcome::Unsatisfiable
}

#[must_use]
#[derive(Eq, PartialEq, Debug)]
enum UnitPropagationOutcome {
    Finished,
    Unsatisfiable,
}

fn unit_propagation<TState: DpllState<TStatistics>, TStatistics: StatsStorage>(
    state: &mut TState,
) -> UnitPropagationOutcome {
    state.start_unit_propagation();

    while let Some(literal) = state.next_unit_literal() {
        state.stats().increment_unit_propagation_steps();

        if state.set_variable_to_literal(literal) == SetVariableOutcome::Unsatisfiable {
            return UnitPropagationOutcome::Unsatisfiable;
        }
    }

    UnitPropagationOutcome::Finished
}
