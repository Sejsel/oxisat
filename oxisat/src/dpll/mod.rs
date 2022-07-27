mod clause_mapping;
mod cnf_transforming;

use crate::dimacs;
use crate::dimacs::Dimacs;
use crate::dpll::clause_mapping::ClauseMappingState;
use crate::dpll::cnf_transforming::CnfTransformingState;

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

    /// Adds a literal to the clause without checking whether this variable is already present.
    ///
    /// # Warning
    /// Adding a literal that is already present will result in undefined behavior.
    pub fn add_literal(&mut self, literal: Literal) {
        self.literals.push(literal)
    }

    /// Adds a literal to the clause.
    ///
    /// Returns `false` if there is already a literal with this variable within this clause.
    #[must_use]
    pub fn add_literal_checked(&mut self, literal: Literal) -> bool {
        if self.contains_variable(literal.variable()) {
            false
        } else {
            self.literals.push(literal);
            true
        }
    }

    /// Adds a literal to the clause without checking whether this variable is already present.
    ///
    /// # Warning
    /// Adding a literal that is already present will result in undefined behavior.
    pub fn add_variable(&mut self, variable: Variable, value: bool) {
        self.literals.push(Literal::new(variable, value))
    }

    /// Adds a literal to the clause.
    ///
    /// Returns `false` if there is already a literal with this variable within this clause.
    #[must_use]
    pub fn add_variable_checked(&mut self, variable: Variable, value: bool) -> bool {
        if self.contains_variable(variable) {
            false
        } else {
            self.literals.push(Literal::new(variable, value));
            true
        }
    }

    fn contains_variable(&self, variable: Variable) -> bool {
        self.literals.iter().any(|x| x.variable() == variable)
    }

    fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    fn is_unit(&self) -> bool {
        self.literals.len() == 1
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

    /// Returns `true` if this CNF cannot be satisfied (i.e. contains an empty clause)
    fn is_unsatisfiable(&self) -> bool {
        self.clauses.iter().any(|clause| clause.is_empty())
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
    Satisfiable(Vec<VariableState>),
    Unsatisfiable,
}

pub enum Implementation {
    Default,
    CnfTransforming,
    ClauseMapping,
}

pub fn solve<TStatistics: StatsStorage>(
    cnf: &CNF,
    implementation: Implementation,
) -> (Solution, TStatistics) {
    match implementation {
        Implementation::Default => solve_cnf::<ClauseMappingState<TStatistics>, TStatistics>(cnf),
        Implementation::CnfTransforming => solve_cnf::<CnfTransformingState<TStatistics>, TStatistics>(cnf),
        Implementation::ClauseMapping => solve_cnf::<ClauseMappingState<TStatistics>, TStatistics>(cnf),
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum VariableState {
    Unset,
    True,
    False,
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

impl From<bool> for VariableState {
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
}

#[derive(Default)]
pub struct NoStats;

#[derive(Default)]
pub struct Stats {
    decisions: u64,
    unit_propagation_steps: u64,
}

impl Stats {
    pub fn decisions(&self) -> u64 {
        self.decisions
    }

    pub fn unit_propagation_steps(&self) -> u64 {
        self.unit_propagation_steps
    }
}

impl StatsStorage for NoStats {
    fn increment_decisions(&mut self) {}
    fn increment_unit_propagation_steps(&mut self) {}
}

impl StatsStorage for Stats {
    fn increment_decisions(&mut self) {
        self.decisions += 1;
    }

    fn increment_unit_propagation_steps(&mut self) {
        self.unit_propagation_steps += 1;
    }
}

trait DpllState<TStats: StatsStorage> {
    fn new(cnf: &CNF, max_variable: Variable) -> Self;
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

fn solve_cnf<TState: DpllState<TStatistics>, TStatistics: StatsStorage>(cnf: &CNF) -> (Solution, TStatistics) {
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

    let mut state = TState::new(cnf, max_variable);
    match dpll(&mut state) {
        DpllDecisionOutcome::Satisfiable => state.into_result(),
        DpllDecisionOutcome::Unsatisfiable => state.into_result(),
    }
}

fn dpll<TState: DpllState<TStatistics>, TStatistics: StatsStorage>(state: &mut TState) -> DpllDecisionOutcome {
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

fn unit_propagation<TState: DpllState<TStatistics>, TStatistics: StatsStorage>(state: &mut TState) -> UnitPropagationOutcome {
    state.start_unit_propagation();

    while let Some(literal) = state.next_unit_literal() {
        state.stats().increment_unit_propagation_steps();

        if state.set_variable_to_literal(literal) == SetVariableOutcome::Unsatisfiable
        {
            return UnitPropagationOutcome::Unsatisfiable;
        }
    }

    UnitPropagationOutcome::Finished
}

#[cfg(test)]
#[generic_tests::define]
mod tests {
    use super::*;

    #[instantiate_tests(<ClauseMappingState<NoStats>>)]
    mod clause_mapping {}

    #[instantiate_tests(<CnfTransformingState<NoStats>>)]
    mod cnf_transforming {}

    #[test]
    fn three_variables_sat<TState: DpllState<NoStats>>() {
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

        let solution = solve_cnf::<TState, NoStats>(&cnf).0;
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn three_variables_unit_propagation_sat<TState: DpllState<NoStats>>() {
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

        let solution = solve_cnf::<TState, NoStats>(&cnf).0;
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn empty_sat<TState: DpllState<NoStats>>() {
        let cnf = CNF::new();

        let solution = solve_cnf::<TState, NoStats>(&cnf).0;
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn empty_clause_unsat<TState: DpllState<NoStats>>() {
        let mut cnf = CNF::new();
        let clause = Clause::new();
        cnf.add_clause(clause);

        let solution = solve_cnf::<TState, NoStats>(&cnf).0;
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn two_conflicting_clause_unsat<TState: DpllState<NoStats>>() {
        let mut cnf = CNF::new();

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), true);
        cnf.add_clause(clause);

        let solution = solve_cnf::<TState, NoStats>(&cnf).0;
        assert!(matches!(solution, Solution::Unsatisfiable));
    }
}
