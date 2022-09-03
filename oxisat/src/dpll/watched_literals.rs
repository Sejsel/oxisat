//! An implementation which uses the watched literals data structure to detect unit clauses.
//! This implementation has two major benefits:
//! - setting a variable only requires updates for watched literals, not all of them
//! - backtracking is almost free (no need to update watched literals)
//!
//! - O(1) amortized find unit clause + O(1) find the unit literal within
//! - O(#clauses (watched ones)) set variable
//! - O(1) undo set variable
//! - O(#vars) find unset variable
use super::*;
use std::mem;

pub struct WatchedState<TStats: StatsStorage> {
    variables: VariableStates,
    change_stack: Vec<ChangeStackItem>,
    clauses: Vec<Clause>,
    watched_literals: WatchedLiteralMap,
    stats: TStats,
    unit_candidate_indices: Vec<usize>,
    newly_watched_clauses: Vec<(Literal, WatchedClause)>,
}

enum ChangeStackItem {
    UnitPropagation,
    SetVariable {
        variable: Variable,
        previous_state: VariableState,
    },
}

struct Clause {
    literals: Vec<Literal>,
    watched_literals: ClauseWatches,
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
}

impl<TStats: StatsStorage> DpllState<TStats> for WatchedState<TStats> {
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
            })
            .collect();

        WatchedState {
            variables: VariableStates::new_unset(max_variable),
            watched_literals: WatchedLiteralMap::from_clauses(&clauses, max_variable),
            newly_watched_clauses: Vec::new(),
            change_stack: Vec::new(),
            stats: Default::default(),
            // The CNF has no unit clauses; this is verified by the assert above.
            unit_candidate_indices: Vec::new(),
            clauses,
        }
    }

    #[inline]
    fn start_unit_propagation(&mut self) {
        self.change_stack.push(ChangeStackItem::UnitPropagation);
    }

    fn undo_last_unit_propagation(&mut self) {
        loop {
            match self.change_stack.pop() {
                Some(ChangeStackItem::UnitPropagation) => {
                    break;
                }
                Some(ChangeStackItem::SetVariable {
                    variable,
                    previous_state,
                }) => self.undo_variable_set_inner(variable, previous_state),
                None => unreachable!("Undoing a unit propagation that did not happen"),
            }
        }
    }

    #[inline]
    fn all_clauses_satisfied(&self) -> bool {
        for i in 0..self.clauses.len() {
            if !self.is_satisfied(i) {
                return false;
            }
        }

        true
    }

    #[inline]
    fn next_unset_variable(&self) -> Option<Variable> {
        // We choose the variable with the lowest index.
        self.variables
            .iter()
            .enumerate()
            .skip(1)
            .find(|(_, &x)| x == VariableState::Unset)
            .map(|(i, _)| Variable::new(i as VariableType))
    }

    fn into_result(self) -> (Solution, TStats) {
        if self.all_clauses_satisfied() {
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
    fn set_variable_to_literal(&mut self, literal: Literal) -> SetVariableOutcome {
        self.set_variable(literal.variable(), literal.value().into())
    }

    fn set_variable(&mut self, variable: Variable, state: VariableState) -> SetVariableOutcome {
        let variable_state = self.variables.get(variable);

        self.change_stack.push(ChangeStackItem::SetVariable {
            variable,
            previous_state: variable_state,
        });
        self.variables.set(variable, state);

        if state != VariableState::Unset {
            let negated_literal = !Literal::new(
                variable,
                match state {
                    VariableState::True => true,
                    VariableState::False => false,
                    VariableState::Unset => unreachable!(),
                },
            );

            // Unfortunately, we cannot use helper methods here as the borrow checker wouldn't
            // understand that we are borrowing separate parts (literals/clauses) of the struct.
            let literal_watches = &mut self.watched_literals.literals
                [WatchedLiteralMap::literal_index(negated_literal)];

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
                        return SetVariableOutcome::Unsatisfiable;
                    }
                }
            }

            mem::swap(
                &mut literal_watches.clauses,
                &mut literal_watches.clauses_new,
            );
            literal_watches.clauses_new.clear();
            self.apply_newly_watched_clauses();
        }

        SetVariableOutcome::Ok
    }

    fn undo_last_set_variable(&mut self) {
        loop {
            match self.change_stack.pop() {
                Some(ChangeStackItem::SetVariable {
                    variable,
                    previous_state,
                }) => {
                    self.undo_variable_set_inner(variable, previous_state);
                    break;
                }
                None => panic!("Undoing a variable that has not been set"),
                Some(ChangeStackItem::UnitPropagation) => {
                    panic!("Undoing across a unit propagation boundary")
                }
            }
        }
    }

    #[inline]
    fn next_unit_literal(&mut self) -> Option<Literal> {
        let clause_index = self.next_unit_clause()?;

        let clause = &self.clauses[clause_index];
        let lit1 = clause.watched_literal1();
        let lit2 = clause.watched_literal2();
        if self.variables.is_unset(lit1.variable()) {
            Some(lit1)
        } else {
            debug_assert!(self.variables.is_unset(lit2.variable()));
            Some(lit2)
        }
    }
}

enum WatchUpdateResult {
    Unchanged,
    Changed,
    NewUnit,
    Unsatisfiable,
}

impl<TStats: StatsStorage> WatchedState<TStats> {
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

impl<TStats: StatsStorage> WatchedState<TStats> {
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

    fn undo_variable_set_inner(&mut self, variable: Variable, previous_state: VariableState) {
        self.variables.set(variable, previous_state);
    }
}
