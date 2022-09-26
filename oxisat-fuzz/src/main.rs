use clap::{ArgEnum, Parser};
use oxisat::{cdcl, dpll};
use oxisat::cnf::*;
use oxisat::sat::Solution;
use rand::prelude::*;
use rand_pcg::Pcg64Mcg;

#[derive(Parser, Debug)]
#[clap(version)]
struct Args {
    #[clap(short, long, arg_enum, default_value_t = Implementation::Cdcl)]
    implementation: Implementation,

    #[clap(short, long, arg_enum, default_value_t = Implementation::DpllWatchedLiterals)]
    reference_implementation: Implementation,

    #[clap(short, long)]
    var_count: VariableType,

    #[clap(short, long)]
    clause_count: usize,

    #[clap(long)]
    min_clause_len: usize,

    #[clap(long)]
    max_clause_len: usize,

    #[clap(long)]
    iters: usize,

    #[clap(long)]
    recreate_seed: Option<String>,
}

#[derive(Debug, Eq, PartialEq, Clone, ArgEnum, Copy)]
enum Implementation {
    DpllCnfTransforming,
    DpllClauseMapping,
    DpllWatchedLiterals,
    Cdcl,
}

fn gen_cnf(args: &Args, seed: [u8; 16]) -> CNF {
    let mut rng: Pcg64Mcg = SeedableRng::from_seed(seed);
    let mut cnf = CNF::new();
    let clause_length = rng.gen_range(args.min_clause_len..=args.max_clause_len);
    for _ in 0..args.clause_count {
        let mut clause = Clause::new();
        for _ in 0..clause_length {
            let var = Variable::new(rng.gen_range(0..args.var_count) + 1);
            clause.add_variable(var, rng.gen());
        }
        cnf.add_clause(clause);
    }
    cnf
}

fn main() {
    let args = Args::parse();

    if let Some(ref seed_string) = args.recreate_seed {
        let seed: [u8; 16] = seed_string
            .split(",")
            .map(|x| x.parse().unwrap())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let cnf = gen_cnf(&args, seed);
        println!("p cnf {} {}", args.var_count, args.clause_count);
        for clause in cnf.clauses() {
            for lit in clause.literals() {
                print!(
                    "{}{} ",
                    if lit.value() { "" } else { "-" },
                    lit.variable().number()
                );
            }
            println!("0");
        }
        println!("0");
        return
    }

    let mut seed_gen = thread_rng();
    for _ in 0..args.iters {
        let seed: [u8; 16] = seed_gen.gen();
        let cnf = gen_cnf(&args, seed);

        println!(
            "[{}]",
            seed.iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(",")
        );
        fn solve(implementation: Implementation, cnf: &CNF) -> Solution
        {
            match implementation {
                Implementation::Cdcl => cdcl::solve::<cdcl::stats::NoStats>(cnf, cdcl::Implementation::Default, Default::default()).0,
                Implementation::DpllWatchedLiterals => dpll::solve::<dpll::stats::NoStats>(cnf, dpll::Implementation::WatchedLiterals).0,
                Implementation::DpllClauseMapping => dpll::solve::<dpll::stats::NoStats>(cnf, dpll::Implementation::ClauseMapping).0,
                Implementation::DpllCnfTransforming => dpll::solve::<dpll::stats::NoStats>(cnf, dpll::Implementation::CnfTransforming).0,
            }
        }
        let solution = solve(args.implementation, &cnf);
        let reference_solution = solve(args.reference_implementation, &cnf);
        let sat = matches!(solution, Solution::Satisfiable(_));
        let ref_sat = matches!(reference_solution, Solution::Satisfiable(_));

        if sat != ref_sat {
            println!("Impl decided SAT={}, Ref impl decided SAT={}", sat, ref_sat);
            println!("p cnf {} {}", args.var_count, args.clause_count);
            for clause in cnf.clauses() {
                for lit in clause.literals() {
                    print!(
                        "{}{} ",
                        if lit.value() { "" } else { "-" },
                        lit.variable().number()
                    );
                }
                println!("0");
            }
            println!("0");
            break;
        } else {
            println!("OK")
        }
    }
}
