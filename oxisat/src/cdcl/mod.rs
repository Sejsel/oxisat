mod state;
pub mod stats;
mod implementation;

#[cfg(test)]
mod tests;

use crate::cdcl::state::Reason;
use crate::cnf::{Literal, Variable, VariableType, CNF};
use crate::preprocessing;
use crate::preprocessing::PreprocessingResult;
use crate::sat::{Solution, VariableResults, VariableValue};
use state::{VariableState, VariableStates};
use stats::StatsStorage;
use implementation::State;

use static_assertions::const_assert;

// We need decision level to be able to go as high as the max variable count.
const_assert!(DecisionLevel::MAX as u128 >= VariableType::MAX as u128);
type DecisionLevel = u32;

trait CdclState<TStats: StatsStorage> {
    fn new(cnf: CNF, max_variable: Variable) -> Self;
    fn decision_level(&self) -> DecisionLevel;
    fn set_decision_level(&mut self, level: DecisionLevel);
    fn all_variables_assigned(&self) -> bool;
    fn pick_branch_literal(&self) -> Option<Literal>;
    fn into_result(self) -> (Solution, TStats);
    fn stats(&mut self) -> &mut TStats;
    fn next_unit_literal(&mut self) -> Option<(Literal, usize)>;
    fn analyze_conflict(&mut self, clause_index: usize) -> ConflictAnalysisResult;
    fn backtrack(&mut self, level: DecisionLevel);
    fn should_restart(&mut self) -> bool;
    fn set_variable_to_literal(&mut self, literal: Literal, reason: Reason) -> SetVariableOutcome;
    fn set_variable(
        &mut self,
        variable: Variable,
        value: bool,
        reason: Reason,
    ) -> SetVariableOutcome;
    fn add_learned_clause(&mut self, literals: Vec<Literal>);
    fn add_learned_lit(&mut self, literal: Literal);
}

pub enum Implementation {
    Default,
    WatchedLiterals,
}

pub fn solve<TStatistics: StatsStorage>(
    cnf: &CNF,
    implementation: Implementation,
) -> (Solution, TStatistics) {
    match implementation {
        Implementation::Default => solve_cnf::<State<TStatistics>, TStatistics>(cnf),
        Implementation::WatchedLiterals => solve_cnf::<State<TStatistics>, TStatistics>(cnf),
    }
}

#[must_use]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum CdclOutcome {
    Satisfiable,
    Unsatisfiable,
}

#[must_use]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum SetVariableOutcome {
    Ok,
    Conflict { clause_index: usize },
}

struct ConflictAnalysisResult {
    backtrack_level: DecisionLevel,
    outcome: ConflictOutcome,
}

enum ConflictOutcome {
    ForcedVariableValue(Literal),
    NewClause(Vec<Literal>),
}

fn solve_cnf_without_variables<TStats: StatsStorage>(cnf: &CNF) -> (Solution, TStats) {
    if cnf.clauses().is_empty() {
        // CNF with no variables
        (
            Solution::Satisfiable(VariableStates::empty().into()),
            Default::default(),
        )
    } else {
        // There is an empty clause, which is unsatisfiable.
        (Solution::Unsatisfiable, Default::default())
    }
}

fn solve_cnf<TState: CdclState<TStats>, TStats: StatsStorage>(cnf: &CNF) -> (Solution, TStats) {
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

                let _ = cdcl(&mut state);
                state.into_result()
            } else {
                solve_cnf_without_variables(&cnf)
            };

            // Map from processed variable space to the pre-processing space.
            (preprocess_result.reverse_map_solution(&solution), stats)
        }
    }
}

fn cdcl<TState: CdclState<TStatistics>, TStatistics: StatsStorage>(
    state: &mut TState,
) -> CdclOutcome {
    state.set_decision_level(0);

    if let UnitPropagationOutcome::Conflict { .. } = unit_propagation(state) {
        return CdclOutcome::Unsatisfiable;
    }

    while !state.all_variables_assigned() {
        state.set_decision_level(state.decision_level() + 1);
        // A literal should always be available as we just checked whether all values are assigned.
        let branch_literal = state.pick_branch_literal().unwrap();
        state.stats().increment_decisions();

        let result = state.set_variable_to_literal(branch_literal, Reason::Decision);
        // This should always be OK, the only way to get a conflict result is to be in
        // the middle of unit propagation.
        debug_assert!(result == SetVariableOutcome::Ok);

        while let UnitPropagationOutcome::Conflict { clause_index } = unit_propagation(state) {
            if state.decision_level() == 0 {
                return CdclOutcome::Unsatisfiable;
            }

            let conflict_result = state.analyze_conflict(clause_index);

            state.backtrack(conflict_result.backtrack_level);

            match conflict_result.outcome {
                ConflictOutcome::NewClause(lits) => {
                    state.stats().increment_learned_clauses();
                    state.add_learned_clause(lits)
                },
                ConflictOutcome::ForcedVariableValue(lit) => {
                    state.stats().increment_learned_literals();
                    state.add_learned_lit(lit)
                },
            }

            if state.should_restart() {
                state.stats().increment_restarts();
                state.backtrack(0);
            }
        }
    }

    CdclOutcome::Satisfiable
}

#[must_use]
#[derive(Eq, PartialEq, Debug)]
enum UnitPropagationOutcome {
    Finished,
    Conflict { clause_index: usize },
}

fn unit_propagation<TState: CdclState<TStatistics>, TStatistics: StatsStorage>(
    state: &mut TState,
) -> UnitPropagationOutcome {
    while let Some((literal, clause_index)) = state.next_unit_literal() {
        state.stats().increment_unit_propagation_steps();

        let reason = Reason::UnitPropagated {
            antecedent_index: clause_index,
        };

        if let SetVariableOutcome::Conflict { clause_index } =
            state.set_variable_to_literal(literal, reason)
        {
            return UnitPropagationOutcome::Conflict { clause_index };
        }
    }

    UnitPropagationOutcome::Finished
}
