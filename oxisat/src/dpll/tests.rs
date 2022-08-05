use super::*;

#[generic_tests::define]
mod dpll {
    use super::*;

    #[instantiate_tests(<ClauseMappingState<NoStats>>)]
    mod clause_mapping {}

    #[instantiate_tests(<CnfTransformingState<NoStats>>)]
    mod cnf_transforming {}

    #[instantiate_tests(<WatchedState<NoStats>>)]
    mod watched_literals {}

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
    fn four_variables_unit_propagation_sat<TState: DpllState<NoStats>>() {
        let mut cnf = CNF::new();

        // Setting any of 1-4 instantly triggers unit propagation that immediately leads to SAT.
        // This also does not get solved by pre-processing.
        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        clause.add_variable(Variable::new(2), true);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(2), false);
        clause.add_variable(Variable::new(3), true);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(3), false);
        clause.add_variable(Variable::new(4), true);
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
