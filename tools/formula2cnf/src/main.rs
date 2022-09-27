use crate::nnf::NNFFormula;
use anyhow::anyhow;
use clap::Parser;
use std::collections::HashMap;
use std::fs::File;
use std::io::{stdin, Read};

mod nnf;

#[derive(Parser, Debug)]
#[clap(version)]
struct Args {
    /// Only use left-to-right implications. Equisatisfiable for NNF formulas.
    #[clap(short, long)]
    one_implication_only: bool,

    /// The simplified SMT-LIB NNF input file.
    #[clap(group = "input")]
    input_file: Option<String>,
}

fn main() -> Result<(), anyhow::Error> {
    let args: Args = Args::parse();

    let input = read_input(args.input_file)?;

    let formula = match nnf::parser::formula(&input) {
        Ok((_, formula)) => formula,
        Err(err) => {
            return Err(anyhow!("Failed to parse formula: {}", err));
        }
    };
    let mode = if args.one_implication_only {
        TseytinMode::LeftToRightImplicationOnly
    } else {
        TseytinMode::Equivalence
    };
    //eprintln!("Parsed formula:");
    //eprintln!("{formula:?}");
    //eprintln!("Transform results:");
    tseytin_transform(&formula, mode);

    Ok(())
}

fn read_input(input_file: Option<String>) -> Result<String, anyhow::Error> {
    let mut input = String::new();
    if let Some(path) = input_file {
        let mut f = File::open(path).expect("Failed to open provided file");
        f.read_to_string(&mut input)
            .expect("Failed to read provided file");
    } else {
        stdin().read_to_string(&mut input)?;
    }

    Ok(input)
}

/// Transforms a NNFFormula using a Tseytin transformation
///
/// # Tseytin or Tseitin transformation?
/// The transformation is named after Григорий Самуилович Цейтин, who uses Gregory S. Tseytin
/// on the English version of his university website. We honor his romanization choice.
fn tseytin_transform(formula: &NNFFormula, mode: TseytinMode) {
    let mut new_variable_index = 0;
    let mut clauses = Vec::new();

    let root = tseytin_transform_inner(formula, &mut new_variable_index, &mut clauses, mode);
    println!("c {} new clauses", clauses.len());

    let mut id_map: HashMap<String, usize> = HashMap::new();

    let mut last_id = 0;
    for clause in &clauses {
        for variable in &clause.variables {
            let name = variable.variable_type.get_name();
            if !id_map.contains_key(&name) {
                last_id += 1;
                println!("c variable {last_id} is {name}");
            }
            id_map.insert(name, last_id);
        }
    }
    println!("c {} is root variable", root.variable_type.get_name());

    let variable_count = last_id;
    let clause_count = clauses.len();
    println!("p cnf {variable_count} {clause_count}");
    for clause in clauses {
        let variables: Vec<_> = clause
            .variables
            .iter()
            .map(|x| {
                let id = id_map.get(&x.variable_type.get_name()).unwrap();
                if x.negated {
                    format!("-{id}")
                } else {
                    format!("{id}")
                }
            })
            .collect();
        println!("{} 0", variables.join(" "))
    }
}

#[derive(Eq, PartialEq, Copy, Clone)]
enum TseytinMode {
    Equivalence,
    LeftToRightImplicationOnly,
}

fn tseytin_transform_inner<'a>(
    formula: &NNFFormula<'a>,
    variable_index: &mut usize,
    clauses: &mut Vec<TseytinClause<'a>>,
    mode: TseytinMode,
) -> TseytinVariable<'a> {
    use TseytinVariableType::{NewVariable, OriginalVariable};

    match formula {
        NNFFormula::Variable(name) => TseytinVariable {
            variable_type: OriginalVariable(name),
            negated: false,
        },
        NNFFormula::Not(formula) => {
            let mut variable = tseytin_transform_inner(formula, variable_index, clauses, mode);
            variable.negate();
            variable
        }
        NNFFormula::And(left, right) => {
            let left_result = tseytin_transform_inner(left, variable_index, clauses, mode);
            let right_result = tseytin_transform_inner(right, variable_index, clauses, mode);

            let new_variable = TseytinVariable::new(NewVariable(*variable_index));
            *variable_index += 1;

            // ¬new ∨ left
            let mut clause = TseytinClause::empty();
            clause.add_variable(new_variable.clone_negated());
            clause.add_variable(left_result.clone());
            clauses.push(clause);

            // ¬new ∨ right
            let mut clause = TseytinClause::empty();
            clause.add_variable(new_variable.clone_negated());
            clause.add_variable(right_result.clone());
            clauses.push(clause);

            if mode == TseytinMode::Equivalence {
                // new ∨ ¬left ∨ ¬right
                let mut clause = TseytinClause::empty();
                clause.add_variable(new_variable.clone());
                clause.add_variable(left_result.clone_negated());
                clause.add_variable(right_result.clone_negated());
                clauses.push(clause);
            }

            new_variable
        }
        NNFFormula::Or(left, right) => {
            let left_result = tseytin_transform_inner(left, variable_index, clauses, mode);
            let right_result = tseytin_transform_inner(right, variable_index, clauses, mode);

            let new_variable = TseytinVariable::new(NewVariable(*variable_index));
            *variable_index += 1;

            // ¬new ∨ left v right
            let mut clause = TseytinClause::empty();
            clause.add_variable(new_variable.clone_negated());
            clause.add_variable(left_result.clone());
            clause.add_variable(right_result.clone());
            clauses.push(clause);

            if mode == TseytinMode::Equivalence {
                // new ∨ ¬left
                let mut clause = TseytinClause::empty();
                clause.add_variable(new_variable.clone());
                clause.add_variable(left_result.clone_negated());
                clauses.push(clause);

                // new ∨ ¬right
                let mut clause = TseytinClause::empty();
                clause.add_variable(new_variable.clone());
                clause.add_variable(right_result.clone_negated());
                clauses.push(clause);
            }

            new_variable
        }
    }
}

struct TseytinClause<'a> {
    variables: Vec<TseytinVariable<'a>>,
}

impl<'a> TseytinClause<'a> {
    pub fn empty() -> Self {
        TseytinClause {
            variables: Vec::new(),
        }
    }

    pub fn add_variable(&mut self, variable: TseytinVariable<'a>) {
        self.variables.push(variable);
    }
}

#[derive(Clone)]
struct TseytinVariable<'a> {
    variable_type: TseytinVariableType<'a>,
    negated: bool,
}

impl<'a> TseytinVariable<'a> {
    pub fn new(variable_type: TseytinVariableType<'a>) -> Self {
        TseytinVariable {
            variable_type,
            negated: false,
        }
    }

    pub fn negate(&mut self) {
        self.negated = !self.negated;
    }

    pub fn clone_negated(&self) -> Self {
        let mut clone = self.clone();
        clone.negate();
        clone
    }
}

#[derive(Clone)]
enum TseytinVariableType<'a> {
    OriginalVariable(&'a str),
    NewVariable(usize),
}

impl<'a> TseytinVariableType<'a> {
    fn get_name(&self) -> String {
        match self {
            TseytinVariableType::OriginalVariable(id) => format!("orig_{id}"),
            TseytinVariableType::NewVariable(name) => format!("aux_{name}"),
        }
    }
}
