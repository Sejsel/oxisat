mod clause_mapping;
mod cnf_transforming;

use crate::dimacs;
use crate::dimacs::Dimacs;

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
    fn value(&self) -> bool {
        self.0 > 0
    }

    /// Returns the variable of the literal.
    fn variable(&self) -> Variable {
        if self.0 > 0 {
            Variable(self.0)
        } else {
            Variable(-self.0)
        }
    }

    fn negated(&self) -> Literal {
        Literal(-self.0)
    }
}

impl std::ops::Not for Literal {
    type Output = Literal;

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
        Implementation::Default => clause_mapping::solve(cnf),
        Implementation::CnfTransforming => cnf_transforming::solve(cnf),
        Implementation::ClauseMapping => clause_mapping::solve(cnf),
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum VariableState {
    Unset,
    True,
    False,
}

impl VariableState {
    pub fn satisfies(&self, literal: Literal) -> bool {
        let literal_state: VariableState = literal.value().into();
        *self == literal_state
    }

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

enum BranchOutcome {
    Satisfiable(Vec<VariableState>),
    Unsatisfiable,
}

impl BranchOutcome {
    fn is_satisfiable(&self) -> bool {
        match self {
            BranchOutcome::Satisfiable(_) => true,
            BranchOutcome::Unsatisfiable => false,
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
