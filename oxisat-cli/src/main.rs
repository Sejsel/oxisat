use anyhow::anyhow;
use clap::{ArgEnum, Parser};
use colored::Colorize;
use comfy_table::Table;
use nom::Finish;
use oxisat::dpll;
use oxisat::dpll::{NoStats, Solution, Stats, VariableState, CNF};
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

    #[clap(short, long, arg_enum, default_value_t = Implementation::DpllClauseMapping)]
    implementation: Implementation,

    #[clap(group = "input")]
    input_file: Option<String>,
}

#[derive(Debug, Eq, PartialEq, Clone, ArgEnum)]
enum Implementation {
    DpllCnfTransforming,
    DpllClauseMapping,
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

    let dpll_impl = match args.implementation {
        Implementation::DpllCnfTransforming => dpll::Implementation::CnfTransforming,
        Implementation::DpllClauseMapping => dpll::Implementation::ClauseMapping,
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
    } else {
        table.add_row(vec!["Decisions", "not tracked"]);
        table.add_row(vec!["Unit propagation derivations", "not tracked"]);
    }
    for line in table.lines() {
        println!("c {line}");
    }
    println!("c");

    match solution {
        Solution::Satisfiable(variables) => {
            println!("s {}", "SATISFIABLE".green());
            let values: Vec<_> = variables
                .iter()
                .enumerate()
                .skip(1)
                .filter(|(_, &state)| state != VariableState::Unset)
                .map(|(i, state)| match state {
                    VariableState::True => format!("{i}"),
                    VariableState::False => format!("-{i}"),
                    VariableState::Unset => unreachable!(),
                })
                .collect();
            println!("v {} 0", values.join(" "));
        }
        Solution::Unsatisfiable => println!("s {}", "UNSATISFIABLE".red()),
    }

    Ok(())
}
