use super::*;

#[derive(Clone, Debug)]
pub enum VariableState {
    Set {
        value: bool,
        decision_level: DecisionLevel,
        reason: Reason,
    },
    Unset,
}

impl VariableState {
    #[inline]
    pub fn is_unset(&self) -> bool {
        matches!(self, VariableState::Unset)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Reason {
    Decision,
    UnitPropagated { antecedent_index: usize },
    Learned,
}

#[derive(Clone)]
pub(crate) struct VariableStates(Vec<VariableState>);

impl VariableStates {
    pub fn new_unset(max_variable: Variable) -> Self {
        // We allocate one extra element to make indexing trivial.
        VariableStates(vec![
            VariableState::Unset;
            (max_variable.number() + 1) as usize
        ])
    }

    pub fn empty() -> Self {
        VariableStates(Vec::new())
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &VariableState> {
        self.0.iter()
    }

    #[inline]
    pub fn satisfies(&self, literal: Literal) -> bool {
        match self.get(literal.variable()) {
            VariableState::Set { value, .. } => *value == literal.value(),
            VariableState::Unset => false,
        }
    }

    #[inline]
    pub fn unsatisfies(&self, literal: Literal) -> bool {
        match self.get(literal.variable()) {
            VariableState::Set { value, .. } => *value != literal.value(),
            VariableState::Unset => false,
        }
    }

    #[inline]
    pub fn is_unset(&self, variable: Variable) -> bool {
        matches!(self.get(variable), VariableState::Unset)
    }

    #[inline]
    pub fn get(&self, variable: Variable) -> &VariableState {
        &self.0[variable.number() as usize]
    }

    #[inline]
    pub fn set(&mut self, variable: Variable, new_state: VariableState) {
        self.0[variable.number() as usize] = new_state
    }
}

impl From<VariableStates> for VariableResults {
    fn from(states: VariableStates) -> Self {
        VariableResults::from_vec(states.iter().map(|x| x.into()).collect())
    }
}

impl From<&VariableState> for VariableValue {
    fn from(state: &VariableState) -> Self {
        match *state {
            VariableState::Set { value: false, .. } => VariableValue::False,
            VariableState::Set { value: true, .. } => VariableValue::True,
            VariableState::Unset => VariableValue::Unset,
        }
    }
}
