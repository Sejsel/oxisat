use super::*;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::mem;

pub(crate) struct State<TStats: StatsStorage, TBranch: BranchingHeuristic> {
    decision_level: DecisionLevel,
    variables: VariableStates,
    variable_stack: Vec<SetUnsetVariable>,
    clauses: Vec<Clause>,
    watched_literals: WatchedLiteralMap,
    unit_candidate_indices: Vec<usize>,
    newly_watched_clauses: Vec<(Literal, WatchedClause)>,
    #[allow(unused)]
    original_clause_count: usize,
    restart_generator: RestartGenerator,
    max_learned_clauses: usize,
    branching_heuristic: TBranch,
    stats: TStats,
}

struct RestartGenerator {
    seq: LubySequence,
    non_resets_since: u64,
}

const MAX_LEARNED_CLAUSES_DEFAULT: usize = 100;
const MAX_LEARNED_CLAUSES_MULT: f32 = 1.1;
const RESTART_RUN_LENGTH: u64 = 100;

impl RestartGenerator {
    fn new() -> Self {
        Self {
            seq: LubySequence::new(),
            non_resets_since: 0,
        }
    }

    fn should_restart(&mut self) -> bool {
        self.non_resets_since += 1;
        if self.non_resets_since >= self.seq.current() * RESTART_RUN_LENGTH {
            self.non_resets_since = 0;
            self.seq.next();
            true
        } else {
            false
        }
    }
}

/// Luby Sequence generator, see OEIS A182105
struct LubySequence {
    u: i64,
    v: i64,
}

impl LubySequence {
    fn new() -> Self {
        Self { u: 1, v: 1 }
    }

    fn current(&self) -> u64 {
        self.v as u64
    }

    fn next(&mut self) -> u64 {
        // Construction by Knuth
        if (self.u & -self.u) == self.v {
            self.u += 1;
            self.v = 1;
        } else {
            self.v *= 2;
        }

        self.v as u64
    }
}

struct SetUnsetVariable {
    variable: Variable,
    decision_level: DecisionLevel,
}

#[derive(Clone)]
struct Clause {
    literals: Vec<Literal>,
    watched_literals: ClauseWatches,
    lbd: u32,
}

impl Clause {
    #[inline]
    fn watched_literal1(&self) -> Literal {
        self.literals[self.watched_literals.watch1.index]
    }

    #[inline]
    fn watched_literal2(&self) -> Literal {
        self.literals[self.watched_literals.watch2.index]
    }

    #[inline]
    fn len(&self) -> usize {
        self.literals.len()
    }
}

#[derive(Copy, Clone)]
struct WatchedClause {
    index: usize,
}

struct LiteralWatches {
    clauses: Vec<WatchedClause>,
    clauses_new: Vec<WatchedClause>,
}

impl LiteralWatches {
    pub fn new() -> Self {
        LiteralWatches {
            clauses: Vec::new(),
            clauses_new: Vec::new(),
        }
    }
}

#[derive(Copy, Clone)]
struct ClauseWatch {
    index: usize,
}

#[derive(Clone)]
struct ClauseWatches {
    watch1: ClauseWatch,
    watch2: ClauseWatch,
}

struct WatchedLiteralMap {
    literals: Vec<LiteralWatches>,
}

impl WatchedLiteralMap {
    fn from_clauses(clauses: &[Clause], max_variable: Variable) -> Self {
        let mut literal_states = Vec::new();
        for _ in 0..((max_variable.number() + 1) * 2) {
            literal_states.push(LiteralWatches::new());
        }

        for (clause_i, clause) in clauses.iter().enumerate() {
            literal_states
                [Self::literal_index(clause.literals[clause.watched_literals.watch1.index])]
            .clauses
            .push(WatchedClause { index: clause_i });
            literal_states
                [Self::literal_index(clause.literals[clause.watched_literals.watch2.index])]
            .clauses
            .push(WatchedClause { index: clause_i });
        }

        Self {
            literals: literal_states,
        }
    }

    #[inline]
    fn literal_mut(&mut self, literal: Literal) -> &mut LiteralWatches {
        &mut self.literals[Self::literal_index(literal)]
    }

    #[inline]
    fn literal_index(literal: Literal) -> usize {
        let offset: usize = if literal.value() { 1 } else { 0 };
        literal.variable().number() as usize * 2 + offset
    }

    fn add_clause(&mut self, clause: &Clause, clause_i: usize) {
        self.literals.push(LiteralWatches::new());

        self.literals[Self::literal_index(clause.literals[clause.watched_literals.watch1.index])]
            .clauses
            .push(WatchedClause { index: clause_i });
        self.literals[Self::literal_index(clause.literals[clause.watched_literals.watch2.index])]
            .clauses
            .push(WatchedClause { index: clause_i });
    }
}

impl<TStats: StatsStorage, TBranch: BranchingHeuristic> CdclState<TStats, TBranch>
    for State<TStats, TBranch>
{
    fn new(cnf: CNF, max_variable: Variable) -> Self {
        for clause in cnf.clauses.iter() {
            assert!(clause.literals.len() > 1);
        }

        let clauses: Vec<_> = cnf
            .clauses
            .into_iter()
            .map(|x| Clause {
                literals: x.literals,
                watched_literals: ClauseWatches {
                    watch1: ClauseWatch { index: 0 },
                    watch2: ClauseWatch { index: 1 },
                },
                // This is not a learned clause, we default to a sane default of 0.
                // This value should not even be looked at for non-learned clauses.
                lbd: 0,
            })
            .collect();

        let mut branching_heuristic: TBranch = Default::default();
        branching_heuristic.initialize(max_variable);

        State {
            decision_level: 0,
            variables: VariableStates::new_unset(max_variable),
            watched_literals: WatchedLiteralMap::from_clauses(&clauses, max_variable),
            newly_watched_clauses: Vec::new(),
            variable_stack: Vec::new(),
            stats: Default::default(),
            // The CNF has no unit clauses; this is verified by the assert above.
            unit_candidate_indices: Vec::new(),
            original_clause_count: clauses.len(),
            restart_generator: RestartGenerator::new(),
            max_learned_clauses: MAX_LEARNED_CLAUSES_DEFAULT,
            branching_heuristic,
            clauses,
        }
    }

    #[inline]
    fn decision_level(&self) -> DecisionLevel {
        self.decision_level
    }

    #[inline]
    fn set_decision_level(&mut self, level: DecisionLevel) {
        self.decision_level = level
    }

    #[inline]
    fn all_variables_assigned(&self) -> bool {
        for i in 0..self.clauses.len() {
            if !self.is_satisfied(i) {
                return false;
            }
        }

        true
    }

    #[inline]
    fn pick_branch_literal(&self) -> Option<Literal> {
        self.branching_heuristic.choose_literal(&self.variables)
    }

    fn into_result(self) -> (Solution, TStats) {
        if self.all_variables_assigned() {
            (Solution::Satisfiable(self.variables.into()), self.stats)
        } else {
            (Solution::Unsatisfiable, self.stats)
        }
    }

    #[inline]
    fn stats(&mut self) -> &mut TStats {
        &mut self.stats
    }

    #[inline]
    fn branching_heuristic(&mut self) -> &mut TBranch {
        &mut self.branching_heuristic
    }

    #[inline]
    fn set_variable_to_literal(&mut self, literal: Literal, reason: Reason) -> SetVariableOutcome {
        self.set_variable(literal.variable(), literal.value(), reason)
    }

    fn set_variable(
        &mut self,
        variable: Variable,
        value: bool,
        reason: Reason,
    ) -> SetVariableOutcome {
        debug_assert!(self.variables.get(variable).is_unset());

        self.variables.set(
            variable,
            VariableState::Set {
                reason,
                decision_level: self.decision_level,
                value,
            },
        );

        self.variable_stack.push(SetUnsetVariable {
            variable,
            decision_level: self.decision_level,
        });

        let negated_literal = !Literal::new(variable, value);

        self.set_variable_update_watches(negated_literal)
    }

    #[inline]
    fn next_unit_literal(&mut self) -> Option<(Literal, usize)> {
        let clause_index = self.next_unit_clause()?;

        let clause = &self.clauses[clause_index];
        let lit1 = clause.watched_literal1();
        let lit2 = clause.watched_literal2();
        if self.variables.is_unset(lit1.variable()) {
            Some((lit1, clause_index))
        } else {
            debug_assert!(self.variables.is_unset(lit2.variable()));
            Some((lit2, clause_index))
        }
    }

    fn analyze_conflict(&mut self, clause_index: usize) -> ConflictAnalysisResult {
        // The top of the change stack has the variable that caused the conflict.
        debug_assert!(!self.variable_stack.is_empty());

        // TODO: save in state and reuse
        let mut clause = self.clauses[clause_index].literals.clone();

        for set_variable in self.variable_stack.iter().rev() {
            match self.variables.get(set_variable.variable) {
                VariableState::Set {
                    reason: Reason::UnitPropagated { antecedent_index },
                    ..
                } => {
                    // TODO: optimize
                    if clause.iter().all(|x| x.variable() != set_variable.variable) {
                        // This variable is not a parent of the conflict
                        continue;
                    }

                    let antecedent = &self.clauses[*antecedent_index];
                    clause = resolve(&clause, &antecedent.literals, set_variable.variable);

                    // TODO: optimize (by keeping track?)
                    let lits_set_at_current_decision_level = clause
                        .iter()
                        .filter(|x| match self.variables.get(x.variable()) {
                            VariableState::Set { decision_level, .. } => {
                                *decision_level == self.decision_level
                            }
                            VariableState::Unset => unreachable!(),
                        })
                        .count();

                    let is_uip = lits_set_at_current_decision_level == 1;
                    if is_uip {
                        break;
                    }
                }
                VariableState::Set {
                    reason: Reason::Decision,
                    value,
                    ..
                } => {
                    let decided_lit = Literal::new(set_variable.variable, *value);
                    return ConflictAnalysisResult {
                        backtrack_level: 0,
                        outcome: ConflictOutcome::ForcedVariableValue(!decided_lit),
                    };
                }
                _ => unreachable!(),
            };
        }

        debug_assert!(!clause.is_empty());

        if clause.len() == 1 {
            return ConflictAnalysisResult {
                backtrack_level: 0,
                outcome: ConflictOutcome::ForcedVariableValue(clause[0]),
            };
        }

        // todo: add fn for this
        // backtrack level = assertion level (second highest in clause)
        let mut assertion_level = 0;
        for &lit in &clause {
            let decision_level = match self.variables.get(lit.variable()) {
                VariableState::Set { decision_level, .. } => *decision_level,
                VariableState::Unset => unreachable!(),
            };
            if decision_level != self.decision_level {
                assertion_level = assertion_level.max(decision_level);
            }
        }

        ConflictAnalysisResult {
            backtrack_level: assertion_level,
            outcome: ConflictOutcome::NewClause(clause),
        }
    }

    fn backtrack(&mut self, level: DecisionLevel) {
        while let Some(SetUnsetVariable {
            variable,
            decision_level,
        }) = self.variable_stack.last()
        {
            if *decision_level > level {
                self.unset_variable(*variable);
            } else {
                break;
            }

            self.variable_stack.pop();
        }

        self.set_decision_level(level);
    }

    fn should_restart(&mut self) -> bool {
        self.restart_generator.should_restart()
    }

    fn add_learned_clause(&mut self, literals: Vec<Literal>) {
        debug_assert!(literals.len() >= 2);

        // TODO: Optimize by using duplication detection
        let lbd = literals
            .iter()
            .map(|x| match self.variables.get(x.variable()) {
                VariableState::Set { decision_level, .. } => *decision_level,
                // There is currently only one unset literal (we used it to choose the backtracking level)
                VariableState::Unset => self.decision_level + 1,
            })
            .unique()
            .count() as u32;

        let mut clause = Clause {
            literals,
            watched_literals: ClauseWatches {
                watch1: ClauseWatch { index: 0 },
                watch2: ClauseWatch { index: 1 },
            },
            lbd,
        };

        // This clause is assertive.
        debug_assert_eq!(
            clause
                .literals
                .iter()
                .filter(|x| self.variables.get(x.variable()).is_unset())
                .count(),
            1
        );

        let unset_var_index = clause
            .literals
            .iter()
            .position(|x| self.variables.get(x.variable()).is_unset())
            .expect("There has to be at least one unset variable in an assertive clause.");

        let (literal_set_on_last_level_index, _) = clause
            .literals
            .iter()
            .enumerate()
            .filter_map(|(i, x)| match self.variables.get(x.variable()) {
                VariableState::Set { decision_level, .. } => Some((i, *decision_level)),
                VariableState::Unset => None,
            })
            .max_by_key(|(_, decision_level)| *decision_level)
            .expect("At least one literal should be set");

        // We need to make sure that the watch state is a valid unit clause state
        // (one watching the unit literal, one watching a literal decided on the last level)
        clause.watched_literals.watch1.index = unset_var_index;
        clause.watched_literals.watch2.index = literal_set_on_last_level_index;

        let clause_i = self.clauses.len();
        self.watched_literals.add_clause(&clause, clause_i);
        self.clauses.push(clause);
        self.unit_candidate_indices.push(clause_i);
    }

    fn add_learned_lit(&mut self, literal: Literal) {
        debug_assert!(self.variables.is_unset(literal.variable()));
        debug_assert!(self.decision_level == 0);

        self.variables.set(
            literal.variable(),
            VariableState::Set {
                reason: Reason::Learned,
                value: literal.value(),
                decision_level: 0,
            },
        );

        match self.set_variable_update_watches(!literal) {
            SetVariableOutcome::Ok => {}
            SetVariableOutcome::Conflict { .. } => {
                unreachable!("A new learned literal should never be conflicting")
            }
        }
    }

    fn restart(&mut self) {
        self.max_learned_clauses =
            (self.max_learned_clauses as f32 * MAX_LEARNED_CLAUSES_MULT).ceil() as usize;

        // No variables are decided at this point.
        debug_assert!(!self.variables.iter().any(|x| matches!(
            x,
            VariableState::Set {
                reason: Reason::Decision,
                ..
            }
        )));

        let antecedent_indices: HashSet<usize> = self
            .variables
            .iter()
            .filter_map(|x| match x {
                VariableState::Set {
                    reason: Reason::UnitPropagated { antecedent_index },
                    ..
                } => Some(*antecedent_index),
                _ => None,
            })
            .collect();

        let original_count = self.clauses.len();

        // TODO: Optimize if needed.
        let learned_clauses = &self.clauses[self.original_clause_count..];
        let kept_clauses: Vec<_> = learned_clauses
            .iter()
            .cloned()
            .enumerate()
            .sorted_by_key(|(index, clause)| {
                (
                    !antecedent_indices.contains(&(self.original_clause_count + *index)),
                    clause.lbd,
                )
            })
            .enumerate()
            .take_while(|(sorted_i, (i, clause))| {
                antecedent_indices.contains(&(self.original_clause_count + *i))
                    || clause.lbd <= 2
                    || *sorted_i <= self.max_learned_clauses
            }) // Keep all clauses that have LBD 2.
            .map(|(_, pair)| pair)
            .collect();

        // Maps old indexes to new indexes
        let old_to_new_map: HashMap<usize, usize> = kept_clauses
            .iter()
            .enumerate()
            .map(|(new, (old, _))| {
                (
                    self.original_clause_count + *old,
                    self.original_clause_count + new,
                )
            })
            .collect();

        let remap_index = |index: &mut usize| {
            if *index < self.original_clause_count {
                return true;
            }
            if let Some(new_index) = old_to_new_map.get(index) {
                *index = *new_index;
                return true;
            }
            false
        };

        // Remap clause indices
        for lit in self.watched_literals.literals.iter_mut() {
            lit.clauses.retain_mut(|x| remap_index(&mut x.index));
        }
        self.unit_candidate_indices.retain_mut(|x| remap_index(x));

        self.clauses.truncate(self.original_clause_count);
        self.clauses
            .extend(kept_clauses.into_iter().map(|(_, clause)| clause));
        self.stats
            .add_deleted_clauses((original_count - self.clauses.len()) as u64);
    }
}

enum WatchUpdateResult {
    Unchanged,
    Changed,
    NewUnit,
    Unsatisfiable,
}

impl<TStats: StatsStorage, TBranch: BranchingHeuristic> State<TStats, TBranch> {
    fn update_watches(
        literal: Literal,
        watched_clause: &WatchedClause,
        variables: &VariableStates,
        newly_watched_clauses: &mut Vec<(Literal, WatchedClause)>,
        clauses: &mut [Clause],
    ) -> WatchUpdateResult {
        let clause = &mut clauses[watched_clause.index];
        let clause_len = clause.len();
        let watches = &mut clause.watched_literals;

        let (mut watch, other_watch) = if clause.literals[watches.watch1.index] == literal {
            (&mut watches.watch1, &watches.watch2)
        } else {
            debug_assert!(clause.literals[watches.watch2.index] == literal);
            (&mut watches.watch2, &watches.watch1)
        };

        let other_watch_lit = clause.literals[other_watch.index];
        if variables.satisfies(other_watch_lit) {
            // This is already satisfied; we do nothing. This is valid as long as we
            // never undo the satisfaction when continuing deeper into the search tree.
            return WatchUpdateResult::Unchanged;
        }

        let mut updated = false;

        if clause_len == 2 {
            // We can never move the watches for clauses with 2 literals.
        } else if clause_len == 3 {
            debug_assert_ne!(watch.index, other_watch.index);

            let index = if watch.index != 0 && other_watch.index != 0 {
                0
            } else if watch.index != 1 && other_watch.index != 1 {
                1
            } else {
                2
            };

            let lit = clause.literals[index];

            if variables.is_unset(lit.variable()) || variables.satisfies(lit) {
                watch.index = index;
                newly_watched_clauses.push((
                    lit,
                    WatchedClause {
                        index: watched_clause.index,
                    },
                ));
                updated = true;
            }
        } else {
            // See I. P. Gent. Optimal implementation of watched literals and more
            // general techniques (2013).

            let mut i = watch.index + 1;
            loop {
                if i >= clause.literals.len() {
                    i = 0;
                }

                if i == watch.index {
                    break;
                }

                let lit = clause.literals[i];
                if (variables.is_unset(lit.variable()) || variables.satisfies(lit))
                    && i != other_watch.index
                {
                    watch.index = i;

                    updated = true;
                    break;
                }

                i += 1;
            }

            if updated {
                newly_watched_clauses.push((
                    clause.literals[watch.index],
                    WatchedClause {
                        index: watched_clause.index,
                    },
                ));
            }
        }

        if !updated {
            // No space for this = this clause is unit or empty
            // We have already checked if it's satisfied from the other watch, so
            // that cannot be the case. There are only two possibilities remaining:
            // - other watch is unset, this clause has now become unit
            // - other watch is set, this clause is currently queued as unit (from
            //   the other watches viewpoint), but it is ultimately unsatisfiable.
            return if variables.is_unset(other_watch_lit.variable()) {
                WatchUpdateResult::NewUnit
            } else {
                WatchUpdateResult::Unsatisfiable
            };
        }

        WatchUpdateResult::Changed
    }
}

impl<TStats: StatsStorage, TBranch: BranchingHeuristic> State<TStats, TBranch> {
    fn set_variable_update_watches(&mut self, negated_literal: Literal) -> SetVariableOutcome {
        // Unfortunately, we cannot use helper methods here as the borrow checker wouldn't
        // understand that we are borrowing separate parts (literals/clauses) of the struct.
        let literal_watches =
            &mut self.watched_literals.literals[WatchedLiteralMap::literal_index(negated_literal)];

        for (i, &watched_clause) in literal_watches.clauses.iter().enumerate() {
            self.stats.increment_clause_state_updates();
            let update_result = Self::update_watches(
                negated_literal,
                &watched_clause,
                &self.variables,
                &mut self.newly_watched_clauses,
                &mut self.clauses,
            );

            match update_result {
                WatchUpdateResult::Unchanged => {
                    literal_watches.clauses_new.push(watched_clause);
                }
                WatchUpdateResult::Changed => {}
                WatchUpdateResult::NewUnit => {
                    literal_watches.clauses_new.push(watched_clause);
                    self.unit_candidate_indices.push(watched_clause.index);
                }
                WatchUpdateResult::Unsatisfiable => {
                    literal_watches.clauses_new.push(watched_clause);
                    // Add remaining clauses as well.
                    // We rely on vec[vec.len()..] = [] here; slicing panics
                    // with higher starting values, but vec.len() is fine.
                    literal_watches
                        .clauses_new
                        .extend_from_slice(&literal_watches.clauses[i + 1..]);

                    mem::swap(
                        &mut literal_watches.clauses,
                        &mut literal_watches.clauses_new,
                    );
                    literal_watches.clauses_new.clear();
                    self.apply_newly_watched_clauses();
                    return SetVariableOutcome::Conflict {
                        clause_index: watched_clause.index,
                    };
                }
            }
        }

        mem::swap(
            &mut literal_watches.clauses,
            &mut literal_watches.clauses_new,
        );
        literal_watches.clauses_new.clear();
        self.apply_newly_watched_clauses();

        SetVariableOutcome::Ok
    }

    fn apply_newly_watched_clauses(&mut self) {
        for (literal, watch) in &self.newly_watched_clauses {
            let literal_watches = &mut self.watched_literals.literal_mut(*literal);
            literal_watches.clauses.push(*watch);
        }
        self.newly_watched_clauses.clear();
    }

    fn next_unit_clause(&mut self) -> Option<usize> {
        // Unit clause candidates may also contain clauses that are not unit anymore.
        // We remove all the clauses from the end that are not unit anymore.
        while let Some(index) = self.unit_candidate_indices.last() {
            if self.is_unit(*index) {
                break;
            } else {
                self.unit_candidate_indices.pop();
            }
        }

        // We do not pop the found index clause as we want to maintain the invariant of all unit
        // clauses being included in `unit_candidate_indices` and it may stay unit after this
        // function is called.
        self.unit_candidate_indices.last().copied()
    }

    fn is_unit(&self, clause_index: usize) -> bool {
        let clause = &self.clauses[clause_index];
        let lit1 = clause.watched_literal1();
        let lit2 = clause.watched_literal2();

        // Exactly one is unsatisfied (the other undecided) and neither is satisfied.
        (self.variables.unsatisfies(lit1) ^ self.variables.unsatisfies(lit2))
            && !self.variables.satisfies(lit1)
            && !self.variables.satisfies(lit2)
    }

    fn is_satisfied(&self, clause_index: usize) -> bool {
        let clause = &self.clauses[clause_index];
        let lit1 = clause.watched_literal1();
        let lit2 = clause.watched_literal2();

        self.variables.satisfies(lit1) || self.variables.satisfies(lit2)
    }

    fn unset_variable(&mut self, variable: Variable) {
        self.variables.set(variable, VariableState::Unset);
    }
}

// TODO: remove need for allocation and optimize
fn resolve(clause: &[Literal], clause2: &[Literal], var: Variable) -> Vec<Literal> {
    debug_assert!(
        (clause.iter().any(|x| *x == Literal::new(var, true))
            && clause2.iter().any(|x| *x == Literal::new(var, false)))
            || (clause.iter().any(|x| *x == Literal::new(var, false))
                && clause2.iter().any(|x| *x == Literal::new(var, true)))
    );

    [clause, clause2]
        .concat()
        .iter()
        .copied()
        .filter(|&x| x.variable() != var)
        .unique()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn luby_sequence_matches_oeis_a182105() {
        // Values taken from the OEIS A182105 listing
        let expected = vec![
            1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4,
            8, 16, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1,
            2, 4, 8, 16, 32, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1,
            1, 2, 1, 1, 2, 4, 8, 16, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8,
        ];

        let mut seq = LubySequence::new();
        for i in 0..(expected.len() - 1) {
            assert_eq!(seq.current(), expected[i]);
            let next_value = seq.next();
            assert_eq!(next_value, expected[i + 1]);
        }
    }
}
