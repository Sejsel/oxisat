use anyhow::anyhow;
use nom::Finish;
use oxisat::dpll;
use oxisat::dpll::{Solution, VariableState, CNF};
use std::env;
use std::fs::File;
use std::io::{stdin, Read};

fn main() -> anyhow::Result<()> {
    let args: Vec<_> = env::args().collect();

    let mut input = String::new();
    if let Some(path) = args.get(1) {
        // TODO: Better error handling
        let mut f = File::open(path).expect("Failed to open provided file");
        f.read_to_string(&mut input).expect("Failed to read provided file");
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

    match dpll::solve(&cnf) {
        Solution::Satisfiable(variables) => {
            println!("s SATISFIABLE");
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
        Solution::Unsatisfiable => println!("s UNSATISFIABLE"),
    }

    Ok(())
}