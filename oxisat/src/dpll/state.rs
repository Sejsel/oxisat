use super::*;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum VariableState {
    False = 0,
    True = 1,
    Unset,
}

impl VariableState {
    #[inline]
    pub fn satisfies(&self, literal: Literal) -> bool {
        let literal_state: VariableState = literal.value().into();
        *self == literal_state
    }

    #[inline]
    pub fn unsatisfies(&self, literal: Literal) -> bool {
        let literal_state_negated: VariableState = (!literal.value()).into();
        *self == literal_state_negated
    }
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
        self.get(literal.variable()).satisfies(literal)
    }

    #[inline]
    pub fn unsatisfies(&self, literal: Literal) -> bool {
        self.get(literal.variable()).unsatisfies(literal)
    }

    #[inline]
    pub fn is_unset(&self, variable: Variable) -> bool {
        self.get(variable) == VariableState::Unset
    }

    #[inline]
    pub fn get(&self, variable: Variable) -> VariableState {
        self.0[variable.number() as usize]
    }

    #[inline]
    pub fn set(&mut self, variable: Variable, new_state: VariableState) {
        self.0[variable.number() as usize] = new_state
    }
}

impl From<bool> for VariableState {
    #[inline]
    fn from(value: bool) -> Self {
        if value {
            VariableState::True
        } else {
            VariableState::False
        }
    }
}

impl From<VariableStates> for VariableResults {
    fn from(states: VariableStates) -> Self {
        VariableResults::from_vec(states.iter().map(|&x| x.into()).collect())
    }
}

impl From<VariableState> for VariableValue {
    fn from(state: VariableState) -> Self {
        match state {
            VariableState::False => VariableValue::False,
            VariableState::True => VariableValue::True,
            VariableState::Unset => VariableValue::Unset,
        }
    }
}

