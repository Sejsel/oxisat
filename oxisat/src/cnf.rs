use crate::dimacs;
use crate::dimacs::Dimacs;

/// The underlying type that is used to handle variables.
/// This is a signed integer type.
pub type VariableType = i32;

pub const MAX_VARIABLE_COUNT: usize = (VariableType::MAX - 1) as usize;

/// Represents a boolean variable without a value.
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Variable(VariableType);

/// Represents a literal, i.e. a variable with a set value (true or false).
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Literal(VariableType);

/// Represents a CNF clause (a disjunction of literals).
#[derive(Clone, Debug)]
pub struct Clause {
    pub(crate) literals: Vec<Literal>,
}

/// Represents a formula in a Conjunctive normal form (a conjunction of disjunction clauses).
#[derive(Clone, Debug)]
pub struct CNF {
    pub(crate) clauses: Vec<Clause>,
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
    #[inline]
    pub const fn new(number: VariableType) -> Self {
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
    #[inline]
    pub const fn new(variable: Variable, is_true: bool) -> Self {
        if is_true {
            Literal(variable.0)
        } else {
            Literal(-variable.0)
        }
    }

    /// Creates a new literal from a raw value, checking whether a valid value has been used.
    #[inline]
    pub const fn from_raw_checked(raw: VariableType) -> Self {
        if raw > 0 {
            Literal::new(Variable::new(raw), true)
        } else if raw < 0 {
            Literal::new(Variable::new(-raw), false)
        } else {
            panic!("Invalid raw value (0 is not permitted)")
        }
    }

    /// Returns `true` if the literal is true.
    #[inline]
    pub fn value(self) -> bool {
        self.0 > 0
    }

    /// Returns the variable of the literal.
    #[inline]
    pub fn variable(self) -> Variable {
        if self.0 > 0 {
            Variable(self.0)
        } else {
            Variable(-self.0)
        }
    }

    /// Returns a negated version of this literal.
    #[inline]
    fn negated(self) -> Literal {
        Literal(-self.0)
    }

    /// Returns the underlying value.
    #[allow(unused)]
    #[inline]
    pub(crate) fn as_raw(self) -> VariableType {
        self.0
    }
}

impl std::ops::Not for Literal {
    type Output = Literal;

    /// Returns a negated version of this literal.
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

    /// Provides the literals contained within the clause.
    #[inline]
    pub fn literals(&self) -> &[Literal] {
        &self.literals
    }

    /// Returns `true` if the clause is unit, i.e. contains only one 1 literal.
    #[inline]
    pub fn is_unit(&self) -> bool {
        self.len() == 1
    }

    /// Returns the number of literals contained within the clause.
    #[inline]
    pub fn len(&self) -> usize {
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

    /// Provides the disjunctive clauses contained within the CNF.
    #[inline]
    pub fn clauses(&self) -> &[Clause] {
        &self.clauses
    }

    /// Returns `true` if this CNF is satisfied (i.e. contains no clauses).
    pub fn is_satisfied(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Returns the maximum variable used within the CNF.
    ///
    /// Runs in O(literals) time.
    pub fn max_variable(&self) -> Option<Variable> {
        self.clauses
            .iter()
            .flat_map(|x| x.literals.iter().map(|x| x.variable()))
            .max()
    }
}
