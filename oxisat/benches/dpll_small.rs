use std::fs::File;
use std::io::Read;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use oxisat::dimacs::Dimacs;
use oxisat::{dimacs, dpll};
use oxisat::dpll::{Clause, NoStats, Stats, Variable, CNF, Implementation};

fn dpll_4v_3c(c: &mut Criterion) {
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
    clause.add_variable(Variable::new(4), false);
    cnf.add_clause(clause);

    let mut group = c.benchmark_group("dpll");
    group.bench_with_input(BenchmarkId::new("cnf_transforming-nostats", "4v-3c"), &cnf, |b, cnf| {
        b.iter(|| dpll::solve::<NoStats>(cnf, Implementation::CnfTransforming))
    });

    group.bench_with_input(BenchmarkId::new("cnf_transforming-stats", "4v-3c"), &cnf, |b, cnf| {
        b.iter(|| dpll::solve::<Stats>(cnf, Implementation::CnfTransforming))
    });
    group.bench_with_input(BenchmarkId::new("clause_mapping-nostats", "4v-3c"), &cnf, |b, cnf| {
        b.iter(|| dpll::solve::<NoStats>(cnf, Implementation::CnfTransforming))
    });

    group.bench_with_input(BenchmarkId::new("clause_mapping-stats", "4v-3c"), &cnf, |b, cnf| {
        b.iter(|| dpll::solve::<Stats>(cnf, Implementation::CnfTransforming))
    });
    group.finish();
}

/// Benchmarks using CNF files from the CaDiCaL project.
fn dpll_cadical_cnf(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpll");
    for instance in ["add4", "prime4", "prime9", "sqrt2809"] {
        let path = format!("{}/tests/cnf/cadical/{instance}.cnf", env!("CARGO_MANIFEST_DIR"));
        let cnf = load_dimacs(path).into();

        group.bench_with_input(BenchmarkId::new("cnf_transforming-nostats", instance), &cnf, |b, cnf| {
            b.iter(|| dpll::solve::<NoStats>(cnf, Implementation::CnfTransforming))
        });

        group.bench_with_input(BenchmarkId::new("cnf_transforming-stats", instance), &cnf, |b, cnf| {
            b.iter(|| dpll::solve::<Stats>(cnf, Implementation::CnfTransforming))
        });

        group.bench_with_input(BenchmarkId::new("clause_mapping-nostats", instance), &cnf, |b, cnf| {
            b.iter(|| dpll::solve::<NoStats>(cnf, Implementation::ClauseMapping))
        });

        group.bench_with_input(BenchmarkId::new("clause_mapping-stats", instance), &cnf, |b, cnf| {
            b.iter(|| dpll::solve::<Stats>(cnf, Implementation::ClauseMapping))
        });

    }
    group.finish();
}

fn load_dimacs(path: String) -> Dimacs {
    let mut input = String::new();
    let mut f = File::open(path).expect("Failed to open provided file");
    f.read_to_string(&mut input).expect("Failed to read provided file");

    let (_, dimacs) = dimacs::parse(&input).expect("Failed to parse DIMACS");
    dimacs
}


criterion_group!(benches, dpll_4v_3c, dpll_cadical_cnf);

criterion_main!(benches);
