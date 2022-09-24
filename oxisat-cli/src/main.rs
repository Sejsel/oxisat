use anyhow::anyhow;
use clap::{ArgEnum, Parser};
use colored::Colorize;
use comfy_table::{CellAlignment, Table};
use nom::Finish;
use oxisat::cnf::CNF;
use oxisat::{cdcl, dpll};
use oxisat::dpll::stats::{NoStats, Stats};
use oxisat::sat::{Solution, VariableValue};
use std::env;
use std::fs::File;
use std::io::{stdin, Read};
use std::time::Instant;

#[derive(Parser, Debug)]
#[clap(version)]
struct Args {
    /// Do not calculate detailed stats; CPU time is still measured.
    #[clap(short, long)]
    no_stats: bool,

    #[clap(short, long, arg_enum, default_value_t = Implementation::Cdcl)]
    implementation: Implementation,

    #[clap(group = "input")]
    input_file: Option<String>,
}

#[derive(Debug, Eq, PartialEq, Clone, ArgEnum)]
enum Implementation {
    Dpll,
    DpllCnfTransforming,
    DpllClauseMapping,
    DpllWatchedLiterals,
    Cdcl,
    CdclVsids,
    CdclLowestIndex,
}

enum Algorithm {
    Dpll,
    Cdcl
}

impl Implementation {
    fn algorithm(&self) -> Algorithm {
        match self {
            Implementation::Dpll => Algorithm::Dpll,
            Implementation::DpllCnfTransforming => Algorithm::Dpll,
            Implementation::DpllClauseMapping => Algorithm::Dpll,
            Implementation::DpllWatchedLiterals => Algorithm::Dpll,
            Implementation::Cdcl => Algorithm::Cdcl,
            Implementation::CdclVsids => Algorithm::Cdcl,
            Implementation::CdclLowestIndex => Algorithm::Cdcl,
        }
    }
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let mut input = String::new();
    if let Some(path) = args.input_file {
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

    println!(
        "c {} {}",
        "oxisat".bright_yellow(),
        env!("CARGO_PKG_VERSION")
    );

    let cnf: CNF = dimacs.into();

    let start_time = Instant::now();

    let solution = match args.implementation.algorithm() {
        Algorithm::Cdcl => {
            let cdcl_impl = match args.implementation {
                Implementation::Cdcl => cdcl::Implementation::Default,
                Implementation::CdclVsids => cdcl::Implementation::BranchVSIDS,
                Implementation::CdclLowestIndex => cdcl::Implementation::BranchLowestIndex,
                Implementation::Dpll => unreachable!(),
                Implementation::DpllCnfTransforming => unreachable!(),
                Implementation::DpllClauseMapping => unreachable!(),
                Implementation::DpllWatchedLiterals => unreachable!(),
            };
            let (solution, stats) = if !args.no_stats {
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
            table.set_header(vec![
                "Stat",
                "Total",
                "/s",
            ]);
            table.get_column_mut(1).unwrap().set_cell_alignment(CellAlignment::Right);
            table.get_column_mut(2).unwrap().set_cell_alignment(CellAlignment::Right);
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
                    &per_sec(stats.decisions())
                ]);
                table.add_row(vec![
                    "Conflicts",
                    &stats.conflicts().to_string(),
                    &per_sec(stats.conflicts())
                ]);
                table.add_row(vec![
                    "Unit propagation derivations",
                    &stats.unit_propagation_steps().to_string(),
                    &per_sec(stats.unit_propagation_steps())
                ]);
                table.add_row(vec![
                    "Clause state updates",
                    &stats.clause_state_updates().to_string(),
                    &per_sec(stats.clause_state_updates())
                ]);
                table.add_row(vec![
                    "Learned clauses",
                    &stats.learned_clauses().to_string(),
                    &per_sec(stats.learned_clauses())
                ]);
                table.add_row(vec![
                    "Learned literals",
                    &stats.learned_literals().to_string(),
                    &per_sec(stats.learned_literals())
                ]);
                table.add_row(vec![
                    "Restarts",
                    &stats.restarts().to_string(),
                    &per_sec(stats.restarts())
                ]);
                table.add_row(vec![
                    "Deleted clauses",
                    &stats.deleted_clauses().to_string(),
                    &per_sec(stats.deleted_clauses())
                ]);
            }
            for line in table.lines() {
                println!("c {line}");
            }
            println!("c");

            solution
        }
        Algorithm::Dpll => {
            let dpll_impl = match args.implementation {
                Implementation::Dpll => dpll::Implementation::Default,
                Implementation::DpllCnfTransforming => dpll::Implementation::CnfTransforming,
                Implementation::DpllClauseMapping => dpll::Implementation::ClauseMapping,
                Implementation::DpllWatchedLiterals => dpll::Implementation::WatchedLiterals,
                Implementation::Cdcl => unreachable!(),
                Implementation::CdclVsids => unreachable!(),
                Implementation::CdclLowestIndex => unreachable!(),
            };

            let (solution, stats) = if !args.no_stats {
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
