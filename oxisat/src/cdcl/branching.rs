use crate::cdcl::state::VariableStates;
use crate::cnf::{Literal, Variable, VariableType};

pub(crate) trait BranchingHeuristic: Default {
    fn initialize(&mut self, max_var: Variable);
    fn choose_literal(&self, states: &VariableStates) -> Option<Literal>;
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

impl BranchingHeuristic for ClausalVSIDS {
    fn initialize(&mut self, max_var: Variable) {
        // We allocate one extra element to make indexing trivial.
        self.weights = vec![1.0; max_var.number() as usize + 1];
        // This prevents the invalid variable being chosen.
        self.weights[0] = 0.0;
    }

    fn choose_literal(&self, states: &VariableStates) -> Option<Literal> {
        // For now, we always choose true by default.
        self.weights
            .iter()
            .enumerate()
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

    fn choose_literal(&self, states: &VariableStates) -> Option<Literal> {
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
