use crate::cnf::{Literal, Variable, VariableType, CNF};
use crate::sat::{Solution, VariableValue, VariableResults};

pub(crate) enum PreprocessingResult {
    /// The original CNF is unsatisfiable.
    Unsatisfiable,
    Preprocessed {
        original_max_variable: Variable,
        new_max_variable: Option<Variable>,
        set_variables: Vec<(Variable, VariableValue)>,
        new_to_old_variable_indices: Vec<(usize, usize)>,
    },
}

impl PreprocessingResult {
    /// Converts a [`Solution`] from the variable space of the post-processed CNF
    /// to the original CNF.
    pub(crate) fn reverse_map_solution(&self, solution: &Solution) -> Solution {
        match solution {
            Solution::Satisfiable(states) => {
                Solution::Satisfiable(self.reverse_map_variables(&states))
            }
            Solution::Unsatisfiable => Solution::Unsatisfiable,
        }
    }

    /// Converts [`VariableStates`] from the variable space of the post-processed CNF
    /// to the original CNF.
    pub(crate) fn reverse_map_variables(&self, states: &VariableResults) -> VariableResults {
        match self {
            PreprocessingResult::Unsatisfiable => states.clone(),
            PreprocessingResult::Preprocessed {
                set_variables,
                original_max_variable,
                new_to_old_variable_indices,
                ..
            } => {
                let mut result = VariableResults::new_unset(*original_max_variable);

                for &(var, state) in set_variables {
                    result.set(var, state);
                }

                for &(new_i, old_i) in new_to_old_variable_indices {
                    if old_i == 0 {
                        continue;
                    }

                    let old_var = Variable::new(old_i as VariableType);
                    let new_var = Variable::new(new_i as VariableType);
                    result.set(old_var, states.get(new_var))
                }

                result
            }
        }
    }
}

impl VariableValue {
    #[inline]
    fn satisfies(&self, literal: Literal) -> bool {
        let literal_state: VariableValue = literal.value().into();
        *self == literal_state
    }

    #[inline]
    fn unsatisfies(&self, literal: Literal) -> bool {
        let literal_state_negated: VariableValue = (!literal.value()).into();
        *self == literal_state_negated
    }
}

pub(crate) fn preprocess_cnf(cnf: &mut CNF, max_variable: Variable) -> PreprocessingResult {
    debug_assert!(cnf
        .max_variable()
        .map(|x| x == max_variable)
        .unwrap_or(true));

    let mut states = VariableResults::new_unset(max_variable);

    // Remove duplicate literals in clauses
    remove_duplicate_literals(cnf, max_variable);

    // Setting variables according to unit clauses. We need to repeat this as more unit clauses
    // may be created by this process.
    //
    // This is currently O(#clauses^2), the worst case scenario creates
    // one unit clause with each iteration.
    // TODO: Improve the worst-case performance by maintaining a list of unit clauses.
    //       (maybe construct use the clause-mapping implementation and just call unit
    //        propagation from that)

    loop {
        let mut any_changed = false;
        for clause in &cnf.clauses {
            if clause.is_unit() {
                let literal = clause.literals[0];
                let state = states.get(literal.variable());

                let opposite_state: VariableValue = (!literal.value()).into();
                if state == opposite_state {
                    return PreprocessingResult::Unsatisfiable;
                }

                states.set_to_literal(literal);
                any_changed = true;
            }
        }

        if !any_changed {
            break;
        }

        let mut any_changed = false;
        for clause in &mut cnf.clauses {
            // Remove literals which are not satisfiable.
            let len_before = clause.len();
            clause.literals.retain(|&literal| {
                let state = states.get(literal.variable());
                !state.unsatisfies(literal)
            });

            if clause.len() != len_before {
                any_changed = true;
            }
        }

        if !any_changed {
            break;
        }
    }

    // Remove clauses that are satisfied.
    cnf.clauses.retain(|clause| {
        !clause.literals.iter().any(|&literal| {
            let state = states.get(literal.variable());
            state.satisfies(literal)
        })
    });

    let set_vars: Vec<_> = states
        .iter()
        .enumerate()
        .filter(|(_, &x)| x != VariableValue::Unset)
        .map(|(i, &x)| (Variable::new(i as VariableType), x))
        .collect();

    let unset_vars: Vec<_> = states
        .iter()
        .enumerate()
        .filter(|(_, &x)| x == VariableValue::Unset)
        .collect();

    let var_index_pairs: Vec<_> = unset_vars
        .iter()
        .enumerate()
        .map(|(new_i, &(old_i, _))| (new_i, old_i))
        .collect();

    let mut old_to_new_mapping = vec![None; (max_variable.number() + 1) as usize];
    for &(new_i, old_i) in &var_index_pairs {
        old_to_new_mapping[old_i] = Some(new_i);
    }

    for clause in &mut cnf.clauses {
        for literal in &mut clause.literals {
            let new_variable = old_to_new_mapping[literal.variable().number() as usize]
                .expect("Clause references a variable that is already resolved.");
            *literal = Literal::new(Variable::new(new_variable as VariableType), literal.value())
        }
    }

    // The 0 variable should always stay unset.
    assert!(!unset_vars.is_empty());

    let new_max_variable = if unset_vars.len() == 1 {
        None
    } else {
        Some(Variable::new((unset_vars.len() - 1) as VariableType))
    };

    PreprocessingResult::Preprocessed {
        new_to_old_variable_indices: var_index_pairs,
        original_max_variable: max_variable,
        set_variables: set_vars,
        new_max_variable,
    }
}

/// Removes duplicate literals within each clause.
fn remove_duplicate_literals(cnf: &mut CNF, max_variable: Variable) {
    // We maintain a list which maps literal -> index of last clause where it was seen.
    let mut last_seen_indices = vec![usize::MAX; (max_variable.number() as usize + 1) * 2];

    // We may need to remove clauses that are already satisfied. This is not a common scenario in
    // inputs, so we do it in another pass. If there are no such clauses, this won't even allocate.
    let mut removed_clauses = Vec::new();

    for (i, clause) in cnf.clauses.iter_mut().enumerate() {
        let mut satisfied = false;
        clause.literals.retain(|literal| {
            let offset = if literal.value() { 1 } else { 0 };
            let index = literal.variable().number() as usize * 2 + offset;

            // Keep the literal unless it was seen in this clause already.
            let retain = last_seen_indices[index] != i;
            last_seen_indices[index] = i;

            // We also check for the negated version of this literal being contained in this clause.
            let negated_offset = if literal.value() { 0 } else { 1 };
            let negated_index = literal.variable().number() as usize * 2 + negated_offset;

            // We cannot break here, but this scenario of a clause containing
            // both a literal and its negation should be rare.
            if last_seen_indices[negated_index] == i {
                satisfied = true;
            }

            retain
        });

        if satisfied {
            removed_clauses.push(i);
        }
    }

    // Remove clauses prepared for removal.
    if !removed_clauses.is_empty() {
        // We expect that `removed_clauses` is sorted.
        let mut removed_clauses_iter = removed_clauses.iter();
        let mut current_removal = removed_clauses_iter.next();
        let mut index = 0;

        cnf.clauses.retain(|_| {
            let mut retain = true;

            if let Some(index_to_remove) = current_removal {
                if index == *index_to_remove {
                    retain = false;
                    current_removal = removed_clauses_iter.next();
                }
            }

            index += 1;

            retain
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cnf::Clause;

    #[test]
    fn preprocess_removes_unit_chain() {
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
        cnf.add_clause(clause);

        // 3 = true
        // 2 -> false
        // 1 -> true
        let max_var = cnf.max_variable().unwrap();
        preprocess_cnf(&mut cnf, max_var);
        assert_eq!(cnf.clauses.len(), 0);
    }

    #[test]
    fn preprocess_removes_unit_clause() {
        let mut cnf = CNF::new();

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        clause.add_variable(Variable::new(2), true);
        clause.add_variable(Variable::new(3), true);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(2), false);
        cnf.add_clause(clause);

        let max_var = cnf.max_variable().unwrap();
        preprocess_cnf(&mut cnf, max_var);
        assert_eq!(cnf.clauses.len(), 1);
    }

    #[test]
    fn variable_mapping_removes_decided() {
        let mut cnf = CNF::new();

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        clause.add_variable(Variable::new(2), true);
        clause.add_variable(Variable::new(3), true);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(2), false);
        cnf.add_clause(clause);

        let max_var = cnf.max_variable().unwrap();
        let result = preprocess_cnf(&mut cnf, max_var);

        if let PreprocessingResult::Preprocessed {
            new_to_old_variable_indices,
            new_max_variable,
            ..
        } = result
        {
            // The old 3 got remapped into 2; old 2 is decided
            let new_i = 2;
            let (_, old_i) = new_to_old_variable_indices
                .iter()
                .find(|(new, _)| *new == new_i)
                .unwrap();
            assert_eq!(*old_i, 3);

            assert_eq!(Some(Variable::new(2)), new_max_variable);

            assert_eq!(cnf.clauses.len(), 1);
            assert_eq!(cnf.clauses[0].len(), 2);
            for lit in &cnf.clauses[0].literals {
                let var = lit.variable();
                assert!(var == Variable::new(1) || var == Variable::new(2));
            }
        }
    }

    #[test]
    fn reverse_mapping() {
        let mut cnf = CNF::new();

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        clause.add_variable(Variable::new(2), true);
        clause.add_variable(Variable::new(3), true);
        cnf.add_clause(clause);

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(2), false);
        cnf.add_clause(clause);

        let max_var = cnf.max_variable().unwrap();
        let result = preprocess_cnf(&mut cnf, max_var);

        let mut potential_map = VariableResults::new_unset(Variable::new(2));
        potential_map.set(Variable::new(1), VariableValue::True);
        potential_map.set(Variable::new(2), VariableValue::True);

        let reversed_mapping = result.reverse_map_variables(&potential_map);
        assert_eq!(reversed_mapping.get(Variable::new(1)), VariableValue::True); // From post-processed
        assert_eq!(reversed_mapping.get(Variable::new(2)), VariableValue::False); // From pre-process
        assert_eq!(reversed_mapping.get(Variable::new(3)), VariableValue::True);
        // From post-processed
    }

    #[test]
    fn removes_duplicate_literals() {
        let mut cnf = CNF::new();

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        clause.add_variable(Variable::new(1), false);
        clause.add_variable(Variable::new(2), true);
        cnf.add_clause(clause);

        let max_var = cnf.max_variable().unwrap();
        preprocess_cnf(&mut cnf, max_var);
        assert_eq!(cnf.clauses.len(), 1);
        assert_eq!(cnf.clauses[0].len(), 2);
    }

    #[test]
    fn removes_clause_with_both_versions_of_literal() {
        let mut cnf = CNF::new();

        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        clause.add_variable(Variable::new(2), true);
        cnf.add_clause(clause);

        // This clause is always satisfied (3 or not 3).
        let mut clause = Clause::new();
        clause.add_variable(Variable::new(3), false);
        clause.add_variable(Variable::new(3), true);
        clause.add_variable(Variable::new(4), false);
        cnf.add_clause(clause);

        let max_var = cnf.max_variable().unwrap();
        preprocess_cnf(&mut cnf, max_var);
        assert_eq!(cnf.clauses.len(), 1);
        assert_eq!(cnf.clauses[0].len(), 2);
    }

    #[test]
    fn duplicated_unit_removed() {
        let mut cnf = CNF::new();

        // Deduplicate and after that becomes unit
        let mut clause = Clause::new();
        clause.add_variable(Variable::new(2), false);
        clause.add_variable(Variable::new(2), false);
        clause.add_variable(Variable::new(2), false);
        cnf.add_clause(clause);

        let max_var = cnf.max_variable().unwrap();
        preprocess_cnf(&mut cnf, max_var);
        assert_eq!(cnf.clauses.len(), 0);
    }

    #[test]
    fn combined() {
        let mut cnf = CNF::new();

        // Deduplicate and after that becomes unit
        let mut clause = Clause::new();
        clause.add_variable(Variable::new(2), false);
        clause.add_variable(Variable::new(2), false);
        clause.add_variable(Variable::new(2), false);
        cnf.add_clause(clause);

        // Always true (2 or not 2):
        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        clause.add_variable(Variable::new(2), false);
        clause.add_variable(Variable::new(2), true);
        cnf.add_clause(clause);

        // Duplicated and always true
        let mut clause = Clause::new();
        clause.add_variable(Variable::new(1), false);
        clause.add_variable(Variable::new(1), true);
        clause.add_variable(Variable::new(1), true);
        cnf.add_clause(clause);

        let max_var = cnf.max_variable().unwrap();
        preprocess_cnf(&mut cnf, max_var);
        assert_eq!(cnf.clauses.len(), 0);
    }
}
