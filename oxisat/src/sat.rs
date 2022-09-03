use crate::cnf::{Literal, Variable};

pub enum Solution {
    Satisfiable(VariableResults),
    Unsatisfiable,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum VariableValue {
    False = 0,
    True = 1,
    Unset,
}

#[derive(Clone)]
pub struct VariableResults(Vec<VariableValue>);

impl VariableResults {
    pub(crate) fn from_vec(values: Vec<VariableValue>) -> Self {
        Self(values)
    }

    pub(crate) fn new_unset(max_variable: Variable) -> Self {
        // We allocate one extra element to make indexing trivial.
        VariableResults(vec![
            VariableValue::Unset;
            (max_variable.number() + 1) as usize
        ])
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &VariableValue> {
        self.0.iter()
    }

    #[inline]
    pub fn get(&self, variable: Variable) -> VariableValue {
        self.0[variable.number() as usize]
    }

    #[inline]
    pub(crate) fn set(&mut self, variable: Variable, new_state: VariableValue) {
        self.0[variable.number() as usize] = new_state
    }

    #[inline]
    pub(crate) fn set_to_literal(&mut self, literal: Literal) {
        self.set(literal.variable(), literal.value().into())
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl From<bool> for VariableValue {
    #[inline]
    fn from(value: bool) -> Self {
        if value {
            VariableValue::True
        } else {
            VariableValue::False
        }
    }
}
