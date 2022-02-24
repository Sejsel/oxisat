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
#[derive(Clone)]
pub struct Clause {
    literals: Vec<Literal>,
}

/// Represents a formula in a Conjunctive normal form (a conjunction of disjunction clauses).
#[derive(Clone)]
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
    fn is_true(&self) -> bool {
        self.0 > 0
    }

    /// Returns `true` if the literal is negated.
    fn is_false(&self) -> bool {
        self.0 < 0
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

    fn literals(&self) -> &Vec<Literal> {
        &self.literals
    }

    fn is_empty(&self) -> bool {
        self.literals.is_empty()
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
        self.clauses.len() == 0
    }

    /// Returns the clauses of the CNF.
    fn clauses(&self) -> &Vec<Clause> {
        &self.clauses
    }

    /// Returns `true` if this CNF cannot be satisfied (i.e. contains an empty clause)
    fn is_unsatisfiable(&self) -> bool {
        self.clauses.iter().any(|clause| clause.is_empty())
    }
}

pub enum Solution {
    Satisfiable(Vec<VariableState>),
    Unsatisfiable,
}

pub fn solve(cnf: &CNF) -> Solution {
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
                Solution::Satisfiable(Vec::new())
            } else {
                // There is an empty clause, which is unsatisfiable.
                Solution::Unsatisfiable
            };
        }
    };

    let mut state = State::new(max_variable, cnf.clone());
    match dpll(&mut state) {
        BranchOutcome::Satisfiable(variables) => Solution::Satisfiable(variables),
        BranchOutcome::Unsatisfiable => Solution::Unsatisfiable,
    }
}

enum BranchOutcome {
    Satisfiable(Vec<VariableState>),
    Unsatisfiable,
}

fn dpll(state: &mut State) -> BranchOutcome {
    // TODO: Unit propagation

    // TODO: Return these results from unit propagation instead of having to compute them separately
    if state.cnf.is_satisfied() {
        return BranchOutcome::Satisfiable(state.variables.clone());
    }
    if state.cnf.is_unsatisfiable() {
        return BranchOutcome::Unsatisfiable;
    }

    // The unsatisfiability check above should ensure there is an unset variable.
    let next_variable = state.first_unset_variable().unwrap();

    state.set_variable(next_variable, VariableState::True);
    let outcome = dpll(state);
    if matches!(outcome, BranchOutcome::Satisfiable(_)) {
        return outcome;
    }
    state.undo_last_set_variable();

    state.set_variable(next_variable, VariableState::False);
    let outcome = dpll(state);
    if matches!(outcome, BranchOutcome::Satisfiable(_)) {
        return outcome;
    }
    state.undo_last_set_variable();

    BranchOutcome::Unsatisfiable
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum VariableState {
    Unset,
    True,
    False,
}

struct State {
    variables: Vec<VariableState>,
    cnf: CNF,
    cnf_change_stack: Vec<CNFStackItem>,
}

enum CNFStackItem {
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

impl State {
    fn new(max_variable: Variable, cnf: CNF) -> Self {
        State {
            // We allocate one extra element to make indexing trivial.
            variables: vec![VariableState::Unset; (max_variable.number() + 1) as usize],
            cnf,
            cnf_change_stack: Vec::new(),
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
            }
        }
    }

    fn set_variable(&mut self, variable: Variable, state: VariableState) {
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
                        // If the clause becomes empty, it is left that way.
                        let clause = &mut self.cnf.clauses[clause_i];
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

        assert!(matches!(solve(&cnf), Solution::Satisfiable(_)));
    }

    #[test]
    fn empty_sat() {
        let cnf = CNF::new();

        assert!(matches!(solve(&cnf), Solution::Satisfiable(_)));
    }

    #[test]
    fn empty_clause_unsat() {
        let mut cnf = CNF::new();
        let mut clause = Clause::new();
        cnf.add_clause(clause);

        assert!(matches!(solve(&cnf), Solution::Unsatisfiable));
    }

    #[test]
    fn two_clause_unsat() {
        let mut cnf = CNF::new();

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), true);
        cnf.add_clause(clause);

        assert!(matches!(solve(&cnf), Solution::Unsatisfiable));
    }
}
