use oxisat::dpll;
use oxisat::dpll::{Clause, CNF, Solution, Variable, VariableState};

fn main() {
    let mut cnf = CNF::new();

    let mut clause = Clause::new();
    clause.add_variable_checked(Variable::new(1), false);
    clause.add_variable_checked(Variable::new(2), true);
    cnf.add_clause(clause);

    let mut clause = Clause::new();
    clause.add_variable_checked(Variable::new(2), false);
    clause.add_variable_checked(Variable::new(3), false);
    cnf.add_clause(clause);

    let mut clause = Clause::new();
    clause.add_variable_checked(Variable::new(3), true);
    clause.add_variable_checked(Variable::new(4), false);
    cnf.add_clause(clause);

    match dpll::solve(&cnf) {
        Solution::Satisfiable(variables) => {
            println!("SAT");
            for (i, state) in variables.iter().enumerate().skip(1) {
                println!("{i} {}", match state {
                    VariableState::Unset => "?",
                    VariableState::True => "true",
                    VariableState::False => "false",
                });
            }
        }
        Solution::Unsatisfiable => println!("UNSAT")
    }
}
