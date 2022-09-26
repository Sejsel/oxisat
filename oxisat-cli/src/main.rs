use anyhow::anyhow;
use clap::{ArgEnum, Parser, Subcommand};
use colored::Colorize;
use comfy_table::{CellAlignment, Table};
use nom::Finish;
use oxisat::cnf::CNF;
use oxisat::dpll::stats::{NoStats, Stats};
use oxisat::sat::{Solution, VariableValue};
use oxisat::{cdcl, dpll};
use rand::prelude::*;
use std::env;
use std::fs::File;
use std::io::{stdin, Read};
use std::time::Instant;

#[derive(Parser, Debug)]
#[clap(version)]
struct Args {
    #[clap(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Run a DPLL solver.
    Dpll {
        #[clap(short, long, arg_enum, default_value_t = DpllImplementation::WatchedLiterals)]
        implementation: DpllImplementation,

        /// Do not calculate detailed stats; CPU time is still measured.
        #[clap(short, long)]
        no_stats: bool,

        /// The DIMACS input file.
        #[clap(group = "input")]
        input_file: Option<String>,
    },
    /// Run a CDCL solver.
    Cdcl {
        /// The branching strategy used for decisions.
        #[clap(short, long, arg_enum, default_value_t = CdclBranching::Vsids)]
        branching: CdclBranching,

        /// Do not calculate detailed stats; CPU time is still measured.
        #[clap(short, long)]
        no_stats: bool,

        /// 64-bit unsigned integer seed.
        #[clap(short, long)]
        seed: Option<u64>,

        /// The DIMACS input file.
        #[clap(group = "input")]
        input_file: Option<String>,
    },
}

#[derive(Debug, Eq, PartialEq, Clone, ArgEnum)]
enum DpllImplementation {
    CnfTransforming,
    ClauseMapping,
    WatchedLiterals,
}

#[derive(Debug, Eq, PartialEq, Clone, ArgEnum)]
enum CdclBranching {
    Vsids,
    LowestIndex,
    Random,
}

fn read_input(input_file: Option<String>) -> Result<CNF, anyhow::Error> {
    let mut input = String::new();
    if let Some(path) = input_file {
        // TODO: Better error handling
        let mut f = File::open(path).expect("Failed to open provided file");
        f.read_to_string(&mut input)
            .expect("Failed to read provided file");
    } else {
        stdin().read_to_string(&mut input)?;
    }

    let dimacs = match oxisat::dimacs::parse(&input).finish() {
        Ok((_, dimacs)) => dimacs,
        Err(err) => {
            return Err(anyhow!(
                "Failed to parse dimacs: {}",
                nom::error::convert_error(input.as_str(), err)
            ));
        }
    };

    let cnf: CNF = dimacs.into();
    Ok(cnf)
}

fn main() -> anyhow::Result<()> {
    let args: Args = Args::parse();

    println!(
        "c {} {}",
        "oxisat".bright_yellow(),
        env!("CARGO_PKG_VERSION")
    );

    let start_time = Instant::now();

    let solution = match args.command {
        Commands::Cdcl {
            branching,
            input_file,
            no_stats,
            seed,
        } => {
            let cnf = read_input(input_file)?;

            let cdcl_impl = match branching {
                CdclBranching::Vsids => cdcl::Implementation::BranchVSIDS,
                CdclBranching::LowestIndex => cdcl::Implementation::BranchLowestIndex,
                CdclBranching::Random => cdcl::Implementation::BranchRandom { seed: match seed {
                    None => {
                        let seed = thread_rng().gen();
                        println!("c Using random seed {seed}");
                        seed
                    },
                    Some(seed) => seed,
                } },
            };
            let (solution, stats) = if !no_stats {
                let (solution, stats) = cdcl::solve::<cdcl::stats::Stats>(&cnf, cdcl_impl);
                (solution, Some(stats))
            } else {
                let (solution, _) = cdcl::solve::<cdcl::stats::NoStats>(&cnf, cdcl_impl);
                (solution, None)
            };

            let elapsed_time = start_time.elapsed();
            println!("c");
            let mut table = Table::new();
            table.load_preset(comfy_table::presets::ASCII_BORDERS_ONLY_CONDENSED);
            table.set_header(vec!["Stat", "Total", "/s"]);
            table
                .get_column_mut(1)
                .unwrap()
                .set_cell_alignment(CellAlignment::Right);
            table
                .get_column_mut(2)
                .unwrap()
                .set_cell_alignment(CellAlignment::Right);
            table.add_row(vec![
                "Time spent",
                &format!("{:.4}s", elapsed_time.as_secs_f64()),
            ]);

            let per_sec = |value: u64| -> String {
                let stat = value as f64 / elapsed_time.as_secs_f64();
                format!("{:.1}", stat)
            };

            if let Some(stats) = stats {
                table.add_row(vec![
                    "Decisions",
                    &stats.decisions().to_string(),
                    &per_sec(stats.decisions()),
                ]);
                table.add_row(vec![
                    "Conflicts",
                    &stats.conflicts().to_string(),
                    &per_sec(stats.conflicts()),
                ]);
                table.add_row(vec![
                    "Unit propagation derivations",
                    &stats.unit_propagation_steps().to_string(),
                    &per_sec(stats.unit_propagation_steps()),
                ]);
                table.add_row(vec![
                    "Clause state updates",
                    &stats.clause_state_updates().to_string(),
                    &per_sec(stats.clause_state_updates()),
                ]);
                table.add_row(vec![
                    "Learned clauses",
                    &stats.learned_clauses().to_string(),
                    &per_sec(stats.learned_clauses()),
                ]);
                table.add_row(vec![
                    "Learned literals",
                    &stats.learned_literals().to_string(),
                    &per_sec(stats.learned_literals()),
                ]);
                table.add_row(vec![
                    "Restarts",
                    &stats.restarts().to_string(),
                    &per_sec(stats.restarts()),
                ]);
                table.add_row(vec![
                    "Deleted clauses",
                    &stats.deleted_clauses().to_string(),
                    &per_sec(stats.deleted_clauses()),
                ]);
            }
            for line in table.lines() {
                println!("c {line}");
            }
            println!("c");

            solution
        }
        Commands::Dpll {
            implementation,
            input_file,
            no_stats,
        } => {
            let cnf = read_input(input_file)?;

            let dpll_impl = match implementation {
                DpllImplementation::CnfTransforming => dpll::Implementation::CnfTransforming,
                DpllImplementation::ClauseMapping => dpll::Implementation::ClauseMapping,
                DpllImplementation::WatchedLiterals => dpll::Implementation::WatchedLiterals,
            };

            let (solution, stats) = if !no_stats {
                let (solution, stats) = dpll::solve::<Stats>(&cnf, dpll_impl);
                (solution, Some(stats))
            } else {
                let (solution, _) = dpll::solve::<NoStats>(&cnf, dpll_impl);
                (solution, None)
            };

            let elapsed_time = start_time.elapsed();
            println!("c");
            let mut table = Table::new();
            table.load_preset(comfy_table::presets::NOTHING);
            table.add_row(vec![
                "Time spent",
                &format!("{:.7}s", elapsed_time.as_secs_f64()),
            ]);

            if let Some(stats) = stats {
                table.add_row(vec!["Decisions", &stats.decisions().to_string()]);
                table.add_row(vec![
                    "Unit propagation derivations",
                    &stats.unit_propagation_steps().to_string(),
                ]);
                table.add_row(vec![
                    "Clause state updates",
                    &stats.clause_state_updates().to_string(),
                ]);
            } else {
                table.add_row(vec!["Decisions", "not tracked"]);
                table.add_row(vec!["Unit propagation derivations", "not tracked"]);
                table.add_row(vec!["Clause state updates", "not tracked"]);
            }
            for line in table.lines() {
                println!("c {line}");
            }
            println!("c");

            solution
        }
    };

    match solution {
        Solution::Satisfiable(variables) => {
            println!("s {}", "SATISFIABLE".green());
            let values: Vec<_> = variables
                .iter()
                .enumerate()
                .skip(1)
                .map(|(i, state)| match state {
                    VariableValue::True => format!("{i}"),
                    VariableValue::False => format!("-{i}"),
                    VariableValue::Unset => format!("-{i}"), // Default to false for unset vars
                })
                .collect();
            println!("v {} 0", values.join(" "));
        }
        Solution::Unsatisfiable => println!("s {}", "UNSATISFIABLE".red()),
    }

    Ok(())
}
