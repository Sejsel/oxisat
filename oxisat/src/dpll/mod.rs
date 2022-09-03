mod clause_mapping;
mod cnf_transforming;
mod state;
pub mod stats;
mod watched_literals;

#[cfg(test)]
mod tests;

use crate::cnf::{Clause, Literal, Variable, VariableType, CNF};
use crate::dpll::clause_mapping::ClauseMappingState;
use crate::dpll::cnf_transforming::CnfTransformingState;
use crate::dpll::state::{VariableState, VariableStates};
use crate::dpll::stats::StatsStorage;
use crate::dpll::watched_literals::WatchedState;
use crate::preprocessing;
use crate::preprocessing::PreprocessingResult;
use crate::sat::{Solution, VariableResults, VariableValue};

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
        Implementation::WatchedLiterals => solve_cnf::<WatchedState<TStatistics>, TStatistics>(cnf),
    }
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
