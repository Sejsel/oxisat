#[derive(Debug)]
pub enum NNFFormula<'a> {
    Variable(&'a str),
    And(Box<NNFFormula<'a>>, Box<NNFFormula<'a>>),
    Or(Box<NNFFormula<'a>>, Box<NNFFormula<'a>>),
    Not(Box<NNFFormula<'a>>),
}

pub mod parser {
    use crate::nnf::NNFFormula;
    use nom::branch::alt;
    use nom::bytes::complete::tag;
    use nom::character::complete::{alphanumeric0, anychar, multispace0};
    use nom::combinator::recognize;
    use nom::error::{Error, ErrorKind, ParseError};
    use nom::sequence::tuple;
    use nom::{AsChar, Err, IResult};

    pub fn formula(i: &str) -> IResult<&str, NNFFormula> {
        alt((and, or, not, variable))(i)
    }

    fn variable(i: &str) -> IResult<&str, NNFFormula> {
        fn char_alpha(i: &str) -> IResult<&str, char> {
            let (i, char) = anychar(i)?;
            if char.is_alpha() {
                Ok((i, char))
            } else {
                Err(Err::Error(Error::from_error_kind(i, ErrorKind::Alpha)))
            }
        }

        let (i, var) = recognize(tuple((char_alpha, alphanumeric0)))(i)?;
        Ok((i, NNFFormula::Variable(var)))
    }

    fn and(i: &str) -> IResult<&str, NNFFormula> {
        let (i, (_, _, _, _, formula_left, _, formula_right, _, _)) = tuple((
            tag("("),
            multispace0,
            tag("and"),
            multispace0,
            formula,
            multispace0,
            formula,
            multispace0,
            tag(")"),
        ))(i)?;

        Ok((
            i,
            NNFFormula::And(formula_left.into(), formula_right.into()),
        ))
    }

    fn or(i: &str) -> IResult<&str, NNFFormula> {
        let (i, (_, _, _, _, formula_left, _, formula_right, _, _)) = tuple((
            tag("("),
            multispace0,
            tag("or"),
            multispace0,
            formula,
            multispace0,
            formula,
            multispace0,
            tag(")"),
        ))(i)?;

        Ok((i, NNFFormula::Or(formula_left.into(), formula_right.into())))
    }

    fn not(i: &str) -> IResult<&str, NNFFormula> {
        let (i, (_, _, _, _, variable, _, _)) = tuple((
            tag("("),
            multispace0,
            tag("not"),
            multispace0,
            variable,
            multispace0,
            tag(")"),
        ))(i)?;

        Ok((i, NNFFormula::Not(variable.into())))
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        pub fn nested_5_parses() {
            let input = "(and (or (and (or x1 (not x4)) (or x3 x9)) (and (or x7 x1) (or x4 x9))) (or (and (or x9 x9) (or (not x4) (not x5))) (and (or x3 (not x6)) (or (not x3) x6))))";
            assert!(formula(input).is_ok());
        }

        #[test]
        pub fn nested_8_parses() {
            let input = "(and (or (and (or (and (or (and x1 (not x4)) (and x3 x9)) (or (and x7 x1) (and x4 x9))) (and (or (and x9 x9) (and (not x4) (not x5))) (or (and x3 (not x6)) (and (not x3) x6)))) (or (and (or (and x2 (not x2)) (and (not x6) (not x1))) (or (and (not x9) x7) (and x9 (not x6)))) (and (or (and x2 x4) (and (not x2) x2)) (or (and (not x5) (not x6)) (and x6 (not x4)))))) (and (or (and (or (and (not x2) x9) (and x3 (not x7))) (or (and (not x9) x6) (and x4 x6))) (and (or (and (not x5) x4) (and (not x4) (not x7))) (or (and (not x3) (not x3)) (and x9 (not x7))))) (or (and (or (and (not x6) x3) (and (not x2) x2)) (or (and x3 (not x2)) (and (not x7) (not x9)))) (and (or (and (not x9) x2) (and (not x6) x5)) (or (and (not x3) (not x1)) (and (not x9) x9)))))) (or (and (or (and (or (and x5 x3) (and (not x3) x6)) (or (and (not x1) x6) (and (not x4) x4))) (and (or (and x2 (not x2)) (and x3 (not x9))) (or (and x5 (not x4)) (and x5 (not x6))))) (or (and (or (and (not x9) (not x2)) (and x4 x6)) (or (and x9 x4) (and x2 x4))) (and (or (and x1 (not x2)) (and x5 (not x4))) (or (and x8 x8) (and (not x4) x2))))) (and (or (and (or (and (not x6) (not x7)) (and (not x1) x1)) (or (and (not x6) x4) (and x4 (not x3)))) (and (or (and (not x3) (not x8)) (and x2 (not x9))) (or (and x1 x2) (and x3 (not x8))))) (or (and (or (and (not x4) (not x1)) (and x7 x7)) (or (and (not x8) (not x7)) (and (not x3) x5))) (and (or (and x1 x6) (and x1 (not x9))) (or (and x1 x3) (and x2 x7)))))))";
            assert!(formula(input).is_ok());
        }

        #[test]
        pub fn toy_5_parses() {
            let input = "(or a1 (and a2 (and a3 (and a4 a5))))";
            assert!(formula(input).is_ok());
        }

        #[test]
        pub fn toy_50_parses() {
            let input = "(or a1 (and a2 (and a3 (and a4 (and a5 (and a6 (and a7 (and a8 (and a9 (and a10 (and a11 (and a12 (and a13 (and a14 (and a15 (and a16 (and a17 (and a18 (and a19 (and a20 (and a21 (and a22 (and a23 (and a24 (and a25 (and a26 (and a27 (and a28 (and a29 (and a30 (and a31 (and a32 (and a33 (and a34 (and a35 (and a36 (and a37 (and a38 (and a39 (and a40 (and a41 (and a42 (and a43 (and a44 (and a45 (and a46 (and a47 (and a48 (and a49 a50)))))))))))))))))))))))))))))))))))))))))))))))))";
            assert!(formula(input).is_ok());
        }

        #[test]
        pub fn toy_100_parses() {
            let input = "(or a1 (and a2 (and a3 (and a4 (and a5 (and a6 (and a7 (and a8 (and a9 (and a10 (and a11 (and a12 (and a13 (and a14 (and a15 (and a16 (and a17 (and a18 (and a19 (and a20 (and a21 (and a22 (and a23 (and a24 (and a25 (and a26 (and a27 (and a28 (and a29 (and a30 (and a31 (and a32 (and a33 (and a34 (and a35 (and a36 (and a37 (and a38 (and a39 (and a40 (and a41 (and a42 (and a43 (and a44 (and a45 (and a46 (and a47 (and a48 (and a49 (and a50 (and a51 (and a52 (and a53 (and a54 (and a55 (and a56 (and a57 (and a58 (and a59 (and a60 (and a61 (and a62 (and a63 (and a64 (and a65 (and a66 (and a67 (and a68 (and a69 (and a70 (and a71 (and a72 (and a73 (and a74 (and a75 (and a76 (and a77 (and a78 (and a79 (and a80 (and a81 (and a82 (and a83 (and a84 (and a85 (and a86 (and a87 (and a88 (and a89 (and a90 (and a91 (and a92 (and a93 (and a94 (and a95 (and a96 (and a97 (and a98 (and a99 a100)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))";
            assert!(formula(input).is_ok());
        }
    }
}
