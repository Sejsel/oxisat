use nom::error::VerboseError;
use nom::IResult;

pub enum Literal {
    Positive(i64),
    Negative(i64),
}

pub struct DimacsClause {
    literals: Vec<Literal>,
}

struct DimacsHeader {
    variable_count: usize,
    clause_count: usize,
}

pub struct Dimacs {
    variable_count: usize,
    clauses: Vec<DimacsClause>,
}

impl Dimacs {
    pub fn variable_count(&self) -> usize {
        self.variable_count
    }

    pub fn clauses(&self) -> &Vec<DimacsClause> {
        &self.clauses
    }
}

impl DimacsClause {
    pub fn literals(&self) -> &Vec<Literal> {
        &self.literals
    }
}

pub fn parse(i: &str) -> IResult<&str, Dimacs, VerboseError<&str>> {
    parser::dimacs(i)
}

mod parser {
    use super::*;
    use nom::bytes::complete::tag;
    use nom::character::complete::u64 as text_u64;
    use nom::character::complete::{char, newline, not_line_ending, space1};
    use nom::character::complete::{i64 as text_i64, space0};
    use nom::combinator::{value, verify};
    use nom::error::{context, VerboseError};
    use nom::multi::{count, many0, separated_list1};
    use nom::sequence::{preceded, tuple};
    use nom::IResult;

    pub(crate) fn dimacs(i: &str) -> IResult<&str, Dimacs, VerboseError<&str>> {
        let (i, (_, header)) = tuple((many0(comment), header))(i)?;

        let (i, clauses) = count(
            preceded(newline, clause(header.variable_count)),
            header.clause_count,
        )(i)?;

        let dimacs = Dimacs {
            variable_count: header.variable_count,
            clauses,
        };

        Ok((i, dimacs))
    }

    fn comment(i: &str) -> IResult<&str, (), VerboseError<&str>> {
        context(
            "comment",
            value((), tuple((char('c'), not_line_ending, newline))),
        )(i)
    }

    fn header(i: &str) -> IResult<&str, DimacsHeader, VerboseError<&str>> {
        let (i, (_, _, _, _, variable_count, _, clause_count, _)) = context(
            "header",
            tuple((
                tag("p"),
                space1,
                tag("cnf"),
                space1,
                text_u64,
                space1,
                text_u64,
                space0,
            )),
        )(i)?;
        Ok((
            i,
            DimacsHeader {
                variable_count: variable_count as usize,
                clause_count: clause_count as usize,
            },
        ))
    }

    fn clause(
        max_variable: usize,
    ) -> impl Fn(&str) -> IResult<&str, DimacsClause, VerboseError<&str>> {
        move |i: &str| {
            // Ensure that the clauses do not contain variables with numbers too high.
            let literal = verify(text_i64, |&literal: &i64| {
                literal.unsigned_abs() as usize <= max_variable
            });

            // Clauses are inconveniently terminated by a single 0.
            let (i, (_, literals, _)) = tuple((
                space0,
                verify(separated_list1(space1, literal), |literals: &Vec<i64>| {
                    *literals.last().unwrap() == 0
                }),
                space0,
            ))(i)?;

            let literals = literals
                .iter()
                .take(literals.len() - 1) // Skips the trailing 0.
                .map(|&var| {
                    if var < 0 {
                        Literal::Negative(-var)
                    } else {
                        Literal::Positive(var)
                    }
                })
                .collect();

            Ok((i, DimacsClause { literals }))
        }
    }
}
