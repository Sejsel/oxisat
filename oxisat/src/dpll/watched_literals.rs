//! TODO
//!
//! - O(?) amortized find unit clause + O(?) find the unit literal within
//! - O(?) set variable
//! - O(?) undo set variable variable
//! - O(?) find unset variable
use super::*;
use std::mem;

pub struct WatchedState<TStats: StatsStorage> {
    variables: VariableStates,
    cnf: CNF,
    change_stack: Vec<ChangeStackItem>,
    watched_literals: WatchedLiteralMap,
    stats: TStats,
    unit_candidate_indices: Vec<usize>,
    newly_watched_clauses: Vec<(Literal, WatchedClause)>,
    unset_var_count: usize,
}

enum ChangeStackItem {
    UnitPropagation,
    SetVariable {
        variable: Variable,
        previous_state: VariableState,
    },
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
    clauses: Vec<ClauseWatches>,
}

impl WatchedLiteralMap {
    fn from_cnf(cnf: &CNF, max_variable: Variable) -> Self {
        let mut literal_states = Vec::new();
        for _ in 0..((max_variable.number() + 1) * 2) {
            literal_states.push(LiteralWatches::new());
        }

        let mut clause_states = Vec::new();

        for (clause_i, clause) in cnf.clauses.iter().enumerate() {
            clause_states.push(ClauseWatches {
                watch1: ClauseWatch { index: 0 },
                watch2: ClauseWatch { index: 1 },
            });
            literal_states[Self::literal_index(clause.literals[0])]
                .clauses
                .push(WatchedClause { index: clause_i });
            literal_states[Self::literal_index(clause.literals[1])]
                .clauses
                .push(WatchedClause { index: clause_i });
        }

        Self {
            literals: literal_states,
            clauses: clause_states,
        }
    }

    #[inline]
    fn literal(&self, literal: Literal) -> &LiteralWatches {
        &self.literals[Self::literal_index(literal)]
    }

    #[inline]
    fn literal_mut(&mut self, literal: Literal) -> &mut LiteralWatches {
        &mut self.literals[Self::literal_index(literal)]
    }

    #[inline]
    fn clause(&self, clause_index: usize) -> &ClauseWatches {
        &self.clauses[clause_index]
    }

    #[inline]
    fn clause_mut(&mut self, clause_index: usize) -> &mut ClauseWatches {
        &mut self.clauses[clause_index]
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

        WatchedState {
            variables: VariableStates::new_unset(max_variable),
            watched_literals: WatchedLiteralMap::from_cnf(&cnf, max_variable),
            newly_watched_clauses: Vec::new(),
            cnf,
            change_stack: Vec::new(),
            stats: Default::default(),
            // The CNF has no unit clauses; this is verified by the assert above.
            unit_candidate_indices: Vec::new(),
            unset_var_count: max_variable.number() as usize,
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
        // This is valid as this is checked right *after* unit propagation.
        // Any conflict leading to an empty clause has to happen through unit propagation, it is
        // not possible to skip it as there is no mechanism to decide two variables at once.
        self.unset_var_count == 0
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
            (Solution::Satisfiable(self.variables), self.stats)
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

        if variable_state != VariableState::Unset && state == VariableState::Unset {
            self.unset_var_count += 1;
        } else if variable_state == VariableState::Unset && state != VariableState::Unset {
            self.unset_var_count -= 1;
        }

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
                let watches = &mut self.watched_literals.clauses[watched_clause.index];
                let clause = &self.cnf.clauses[watched_clause.index];

                let (mut watch, other_watch) =
                    if clause.literals[watches.watch1.index].variable() == variable {
                        (&mut watches.watch1, &watches.watch2)
                    } else {
                        debug_assert!(clause.literals[watches.watch2.index].variable() == variable);
                        (&mut watches.watch2, &watches.watch1)
                    };

                let other_watch_lit = clause.literals[other_watch.index];
                if self.variables.satisfies(other_watch_lit) {
                    // This is already satisfied; we do nothing. This is valid as long as we
                    // never undo the satisfaction when continuing deeper into the search tree.
                    literal_watches.clauses_new.push(watched_clause);
                    continue;
                }

                if self.variables.satisfies(clause.literals[watch.index]) {
                    // This is newly satisfied, we do nothing in this clause.
                    literal_watches.clauses_new.push(watched_clause);
                    continue;
                }

                let mut updated = false;

                // TODO: Rewrite going up from current literal pos and then start from 0 again.
                //       (this is required for optimality)
                //        see I. P. Gent. Optimal implementation of watched literals and more
                //        general techniques (2013).
                for (i, lit) in clause.literals.iter().enumerate() {
                    if (self.variables.get(lit.variable()) == VariableState::Unset
                        || self.variables.satisfies(*lit))
                        && i != other_watch.index
                    {
                        watch.index = i;

                        // We store watch updates for applying later as we are (correctly) prevented
                        // by the borrow checker from doing it here (we are already borrowing the
                        // current list from the vec, and there is nothing preventing us from
                        // finding the same literal, even though we do avoid that scenario by
                        // preprocessing). It might be possible to use split_at_mut and choose
                        // the correct slice depending on the index, but this solution is
                        // simpler and correctly handles duplicate literals within one clause.

                        // Instead of allocating a Vec buffer for this every time, we keep one Vec
                        // that we clear after every update and reuse it.
                        self.newly_watched_clauses.push((
                            *lit,
                            WatchedClause {
                                index: watched_clause.index,
                            },
                        ));
                        updated = true;
                        break;
                    }
                }

                if !updated {
                    literal_watches.clauses_new.push(watched_clause);
                    // No space for this = this clause is unit or empty
                    // We have already checked if it's satisfied from the other watch, so
                    // that cannot be the case. There are only two possibilities remaining:
                    // - other watch is unset, this clause has now become unit
                    // - other watch is set, this clause is currently queued as unit (from
                    //   the other watches viewpoint), but it is ultimately unsatisfiable.
                    if self.variables.get(other_watch_lit.variable()) == VariableState::Unset {
                        self.unit_candidate_indices.push(watched_clause.index);
                    } else {
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

        let watch = self.watched_literals.clause(clause_index);
        let lit1 = self.cnf.clauses[clause_index].literals[watch.watch1.index];
        let lit2 = self.cnf.clauses[clause_index].literals[watch.watch2.index];
        if self.variables.get(lit1.variable()) == VariableState::Unset {
            Some(lit1)
        } else {
            debug_assert!(self.variables.get(lit2.variable()) == VariableState::Unset);
            Some(lit2)
        }
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
        let watch = self.watched_literals.clause(clause_index);
        let lit1 = self.cnf.clauses[clause_index].literals[watch.watch1.index];
        let lit2 = self.cnf.clauses[clause_index].literals[watch.watch2.index];

        // Exactly one is unsatisfied (the other undecided) and neither is satisfied.
        (self.variables.unsatisfies(lit1) ^ self.variables.unsatisfies(lit2))
            && !self.variables.satisfies(lit1)
            && !self.variables.satisfies(lit2)
    }

    fn is_satisfied(&self, clause_index: usize) -> bool {
        let watch = self.watched_literals.clause(clause_index);
        let lit1 = self.cnf.clauses[clause_index].literals[watch.watch1.index];
        let lit2 = self.cnf.clauses[clause_index].literals[watch.watch2.index];

        self.variables.satisfies(lit1) || self.variables.satisfies(lit2)
    }

    fn undo_variable_set_inner(&mut self, variable: Variable, previous_state: VariableState) {
        let current_state = self.variables.get(variable);

        if current_state != VariableState::Unset && previous_state == VariableState::Unset {
            self.unset_var_count += 1;
        } else if current_state == VariableState::Unset && previous_state != VariableState::Unset {
            self.unset_var_count -= 1;
        }

        self.variables.set(variable, previous_state);
    }
}
