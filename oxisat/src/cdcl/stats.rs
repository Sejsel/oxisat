pub trait StatsStorage: Default {
    fn increment_decisions(&mut self);
    fn increment_unit_propagation_steps(&mut self);
    fn increment_clause_state_updates(&mut self);
}

#[derive(Default)]
pub struct NoStats;

#[derive(Default)]
pub struct Stats {
    decisions: u64,
    unit_propagation_steps: u64,
    clause_state_updates: u64,
}

impl Stats {
    pub fn decisions(&self) -> u64 {
        self.decisions
    }

    pub fn unit_propagation_steps(&self) -> u64 {
        self.unit_propagation_steps
    }

    pub fn clause_state_updates(&self) -> u64 {
        self.clause_state_updates
    }
}

impl StatsStorage for NoStats {
    #[inline(always)]
    fn increment_decisions(&mut self) {}
    #[inline(always)]
    fn increment_unit_propagation_steps(&mut self) {}
    #[inline(always)]
    fn increment_clause_state_updates(&mut self) {}
}

impl StatsStorage for Stats {
    #[inline]
    fn increment_decisions(&mut self) {
        self.decisions += 1;
    }

    #[inline]
    fn increment_unit_propagation_steps(&mut self) {
        self.unit_propagation_steps += 1;
    }

    #[inline]
    fn increment_clause_state_updates(&mut self) {
        self.clause_state_updates += 1;
    }
}
