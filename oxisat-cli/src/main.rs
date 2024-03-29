use anyhow::anyhow;
use clap::{ArgEnum, Parser, Subcommand};
use colored::Colorize;
use comfy_table::{CellAlignment, Table};
use nom::Finish;
use oxisat::cnf::{CNF, Literal, VariableType};
use oxisat::dpll::stats::{NoStats, Stats};
use oxisat::sat::{Solution, VariableValue};
use oxisat::{cdcl, dpll};
use rand::prelude::*;
use std::env;
use std::fs::File;
use std::io::{stdin, Read};
use std::time::Instant;
use oxisat::cdcl::ParamsConfig;

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
        #[clap(short, long, arg_enum, default_value_t = CdclBranching::VsidsLit)]
        branching: CdclBranching,

        /// Do not calculate detailed stats; CPU time is still measured.
        #[clap(short, long)]
        no_stats: bool,

        /// Assumptions to be applied as first decisions, as a list of clauses, e.g. "1 -2 5 7"
        #[clap(short, long)]
        #[clap(allow_hyphen_values = true)]
        assumptions: Option<String>,

        /// 64-bit unsigned integer seed (used only with random branching).
        #[clap(short, long)]
        seed: Option<u64>,

        /// The amount of restarts done before the restart sequence is evaluated again.
        #[clap(long, default_value_t = 100)]
        restart_run_length: u64,

        /// The default count of max learned clauses. Exceptional clauses may be kept above this limit.
        #[clap(long, default_value_t = 500)]
        max_learned_clauses_default: usize,

        /// The added count which increases the max learned clauses count with each restart.
        #[clap(long, default_value_t = 10)]
        max_learned_clauses_add: usize,

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
    VsidsVar,
    VsidsLit,
    JeroslowWang,
    LowestIndex,
    Random,
}

fn read_input(input_file: Option<String>) -> Result<CNF, anyhow::Error> {
    let mut input = String::new();
    if let Some(path) = input_file {
        let mut f = File::open(path)?;
        f.read_to_string(&mut input)?;
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
            assumptions,
            restart_run_length,
            max_learned_clauses_default,
            max_learned_clauses_add,
            input_file,
            no_stats,
            seed,
        } => {
            let cnf = read_input(input_file)?;

            let params = ParamsConfig {
                restart_run_length,
                max_learned_clauses_default,
                max_learned_clauses_add,
            };

            if branching != CdclBranching::Random && seed != None {
                println!("c WARNING: seed is not used for anything without random branching.")
            }

            let cdcl_impl = match branching {
                CdclBranching::VsidsVar => cdcl::Implementation::BranchVSIDSVar,
                CdclBranching::VsidsLit => cdcl::Implementation::BranchVSIDSLit,
                CdclBranching::LowestIndex => cdcl::Implementation::BranchLowestIndex,
                CdclBranching::JeroslowWang => cdcl::Implementation::JeroslowWang,
                CdclBranching::Random => cdcl::Implementation::BranchRandom {
                    seed: match seed {
                        None => {
                            let seed = thread_rng().gen();
                            println!("c Using random seed {seed}");
                            seed
                        }
                        Some(seed) => seed,
                    },
                },
            };

            let mut ass = Vec::new();
            if let Some(assumption_str) = assumptions {
                let values: Result<Vec<VariableType>, std::num::ParseIntError> = assumption_str.split_whitespace().map(|lit| lit.parse::<VariableType>()).collect();
                let values: Vec<VariableType> = values?;
                for &value in &values {
                    if value == 0 {
                        return Err(anyhow!("Assumption cannot use variable 0."));
                    }

                    if let Some(max_var) = cnf.max_variable() {
                        if value.abs() > max_var.number().abs() {
                            return Err(anyhow!("Assumption {value} is not a valid literal (variable index too high)."));
                        }
                    } else {
                        return Err(anyhow!("Cannot use assumptions for problem with no variables."));
                    }
                }

                ass.extend(values.iter().map(|x| Literal::from_raw_checked(*x)));
            }

            let (solution, stats) = if !no_stats {
                let (solution, stats) = cdcl::solve::<cdcl::stats::Stats>(&cnf, cdcl_impl, params, &ass);
                (solution, Some(stats))
            } else {
                let (solution, _) = cdcl::solve::<cdcl::stats::NoStats>(&cnf, cdcl_impl, params, &ass);
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
