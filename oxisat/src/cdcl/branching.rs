use crate::cdcl::state::VariableStates;
use crate::cnf::{Literal, Variable, VariableType};
use rand::{Rng, SeedableRng};

pub(crate) trait BranchingHeuristic {
    fn initialize(&mut self, max_var: Variable);
    fn choose_literal(&mut self, states: &VariableStates) -> Option<Literal>;
    fn register_new_clause(&mut self, clause_literals: &[Literal]);
}

/// Clausal variant of the VSIDS (Variable State Independent Decaying Sum) heuristic.
///
/// This heuristic does not consider literals that are used for conflict analysis, only
/// literals from the resulting clause.
///
/// This is a variant of VSIDS used by the Chaff solver.
#[derive(Default)]
pub struct ClausalVSIDS {
    weights: Vec<f32>,
}

/// This heuristic chooses the unset variable with the lowest index.
#[derive(Default)]
pub struct LowestIndex {}

/// This heuristic chooses a random value for a random unassigned literal.
pub struct RandomChoice<T: Rng> {
    rng: T,
}

impl BranchingHeuristic for ClausalVSIDS {
    fn initialize(&mut self, max_var: Variable) {
        // We allocate one extra element to make indexing trivial.
        self.weights = vec![1.0; max_var.number() as usize + 1];
        // This prevents the invalid variable being chosen.
        self.weights[0] = 0.0;
    }

    fn choose_literal(&mut self, states: &VariableStates) -> Option<Literal> {
        // For now, we always choose true by default.
        self.weights
            .iter()
            .enumerate()
            .skip(1)
            .filter(|(i, _)| states.is_unset(Variable::new(*i as VariableType)))
            .max_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap())
            .map(|(i, _)| Literal::new(Variable::new(i as VariableType), true))
    }

    fn register_new_clause(&mut self, clause_literals: &[Literal]) {
        for lit in clause_literals {
            self.weights[lit.variable().number() as usize] += 1.0;
        }

        for weight in self.weights.iter_mut() {
            *weight *= 0.95;
        }
    }
}

impl BranchingHeuristic for LowestIndex {
    #[inline]
    fn initialize(&mut self, _: Variable) {}

    fn choose_literal(&mut self, states: &VariableStates) -> Option<Literal> {
        states
            .iter()
            .enumerate()
            .skip(1)
            .find(|(_, x)| x.is_unset())
            .map(|(i, _)| Literal::new(Variable::new(i as VariableType), true))
    }

    #[inline(always)]
    fn register_new_clause(&mut self, _: &[Literal]) {}
}

impl<T: Rng> BranchingHeuristic for RandomChoice<T> {
    #[inline]
    fn initialize(&mut self, _: Variable) {}

    fn choose_literal(&mut self, states: &VariableStates) -> Option<Literal> {
        let count = states.iter().skip(1).filter(|x| x.is_unset()).count();
        if count > 0 {
            let index = self.rng.gen_range(0..count);

            let var_i = states
                .iter()
                .enumerate()
                .skip(1)
                .filter(|(_, var)| var.is_unset())
                .skip(index)
                .map(|(i, _)| i)
                .next()
                .unwrap();

            Some(Literal::new(
                Variable::new(var_i as VariableType),
                self.rng.gen(),
            ))
        } else {
            None
        }
    }

    #[inline(always)]
    fn register_new_clause(&mut self, _: &[Literal]) {}
}

impl<T: Rng + SeedableRng> RandomChoice<T> {
    pub(crate) fn from_u64_seed(seed: u64) -> Self {
        Self {
            rng: T::seed_from_u64(seed)
        }
    }
}