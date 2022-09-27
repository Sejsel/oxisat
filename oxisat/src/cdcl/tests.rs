use super::*;

#[generic_tests::define]
mod cdcl {
    use super::stats::NoStats;
    use super::*;
    use crate::cnf::Clause;
    use crate::dimacs;

    #[instantiate_tests(<State<NoStats, ClausalVarVSIDS>, _>)]
    mod vsids_var {}

    #[instantiate_tests(<State<NoStats, ClausalLitVSIDS>, _>)]
    mod vsids_lit {}

    #[instantiate_tests(<State<NoStats, LowestIndex>, _>)]
    mod lowest_index {}

    #[test]
    fn three_clause_sat<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
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

        let solution = solve_cnf::<TState, _, _>(&cnf, Default::default(), Default::default()).0;
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn three_variables_unit_propagation_sat<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
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

        let solution = solve_cnf::<TState, _, _>(&cnf, Default::default(), Default::default()).0;
        assert!(matches!(solution, Solution::Satisfiable(_)));

        // This is checked to verify pre-processing variable mapping is reversed in case
        // this is solved immediately during pre-processing.
        match solution {
            Solution::Satisfiable(solution) => {
                // One extra for the unused 0 variable.
                assert_eq!(solution.len(), 4);
            }
            Solution::Unsatisfiable => {}
        }
    }

    #[test]
    fn four_variables_unit_propagation_sat<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
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

        let solution = solve_cnf::<TState, _, _>(&cnf, Default::default(), Default::default()).0;
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn empty_sat<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let cnf = CNF::new();

        let solution = solve_cnf::<TState, _, _>(&cnf, Default::default(), Default::default()).0;
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn empty_clause_unsat<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let mut cnf = CNF::new();
        let clause = Clause::new();
        cnf.add_clause(clause);

        let solution = solve_cnf::<TState, _, _>(&cnf, Default::default(), Default::default()).0;
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn two_conflicting_clause_unsat<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let mut cnf = CNF::new();

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), true);
        cnf.add_clause(clause);

        let solution = solve_cnf::<TState, _, _>(&cnf, Default::default(), Default::default()).0;
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    macro_rules! solve_cadical_test {
        ($name:expr) => {{
            let input = include_str!(concat!("../../tests/cnf/cadical/", $name, ".cnf"));
            let (_, dimacs) = dimacs::parse(input).expect("failed to parse");
            let cnf = CNF::from(dimacs);
            solve_cnf::<TState, _, _>(&cnf, Default::default(), Default::default()).0
        }};
    }

    #[test]
    fn cadical_empty<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("empty");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }
    #[test]
    fn cadical_false<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("false");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_unit0<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("unit0");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_unit1<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("unit1");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_unit2<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("unit2");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_unit3<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("unit3");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_unit4<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("unit4");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_unit5<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("unit5");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_unit6<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("unit6");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_unit7<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("unit7");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_sub0<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sub0");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sat0<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat0");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_sat1<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat1");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sat2<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat2");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sat3<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat3");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sat4<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat4");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sat5<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat5");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_sat6<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat6");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sat7<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat7");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sat8<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat8");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sat9<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat9");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sat10<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat10");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sat11<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat11");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sat12<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat12");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sat13<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("sat13");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_full1<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("full1");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_full2<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("full2");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_full3<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("full3");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_full4<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("full4");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_full5<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("full5");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_full6<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("full6");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_full7<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("full7");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_regr000<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("regr000");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_elimclash<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("elimclash");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_elimredundant<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("elimredundant");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_block0<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("block0");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime4<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime4");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime9<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime9");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime25<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime25");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime49<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime49");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime121<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime121");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime169<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime169");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime361<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime361");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime289<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime289");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime529<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime529");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime841<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime841");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime961<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime961");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime1369<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime1369");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime1681<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime1681");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime1849<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime1849");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_prime2209<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("prime2209");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_factor2708413neg<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("factor2708413neg");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_factor2708413pos<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("factor2708413pos");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt2809<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt2809");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt3481<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt3481");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt3721<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt3721");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt4489<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt4489");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt5041<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt5041");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt5329<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt5329");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt6241<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt6241");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt6889<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt6889");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt7921<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt7921");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt9409<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt9409");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt10201<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt10201");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt10609<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt10609");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt11449<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt11449");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt11881<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt11881");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt12769<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt12769");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt16129<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt16129");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt63001<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt63001");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt259081<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt259081");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_sqrt1042441<
        TState: CdclState<NoStats, TBranch>,
        TBranch: BranchingHeuristic + Default,
    >() {
        let solution = solve_cadical_test!("sqrt1042441");
        assert!(matches!(solution, Solution::Satisfiable(_)));
    }

    #[test]
    fn cadical_ph2<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("ph2");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_ph3<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("ph3");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_ph4<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("ph4");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_ph5<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("ph5");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_ph6<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("ph6");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_add4<TState: CdclState<NoStats, TBranch>, TBranch: BranchingHeuristic + Default>() {
        let solution = solve_cadical_test!("add4");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    /*
    The following tests take too long for comfortable testing with pure DPLL:

    #[test]
    fn cadical_add8<TState: DpllState<NoStats>>() {
        let solution = solve_cadical_test!("add8");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_add16<TState: DpllState<NoStats>>() {
        let solution = solve_cadical_test!("add16");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_add32<TState: DpllState<NoStats>>() {
        let solution = solve_cadical_test!("add32");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_add64<TState: DpllState<NoStats>>() {
        let solution = solve_cadical_test!("add64");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_add128<TState: DpllState<NoStats>>() {
        let solution = solve_cadical_test!("add128");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }

    #[test]
    fn cadical_prime65537<TState: DpllState<NoStats>>() {
        let solution = solve_cadical_test!("prime65537");
        assert!(matches!(solution, Solution::Unsatisfiable));
    }
    */
}
