mod scanner;

use self::scanner::Scanner;
use crate::{
    primitives::{self, Assig},
    RuleInstruction,
};
use std::{fmt::Debug, io::BufRead};

pub fn program<'a>(input: impl BufRead + 'a) -> impl IntoIterator<Item = Vec<Assig>> + 'a {
    let mut iter = input.lines();
    let mut next_line;
    loop {
        next_line = iter.next().unwrap().unwrap().trim().to_owned();
        if !(next_line.is_empty() || next_line.starts_with("c")) {
            break;
        }
    }
    let mut scanner = Scanner::new(next_line, iter);
    assert_eq!(scanner.next_token(), Some("p".to_owned()));
    assert_eq!(scanner.next_token(), Some("cnf".to_owned()));
    let _nvars = scanner.next_usize();
    let nclauses = scanner.next_usize();

    RuleReader(ProofReader {
        scanner,
        index: 0,
        expected: Some(nclauses),
    })
}

pub fn proof<'a>(input: impl BufRead + 'a) -> impl Iterator<Item = RuleInstruction> + 'a {
    let scanner = Scanner::new("".to_string(), input.lines());
    ProofReader {
        scanner,
        index: 0,
        expected: None,
    }
}

struct ProofReader<L: Iterator> {
    scanner: Scanner<L>,
    index: usize,
    expected: Option<usize>,
}

impl<Err: Debug, L: Iterator<Item = Result<String, Err>>> Iterator for ProofReader<L> {
    type Item = RuleInstruction;

    fn next(&mut self) -> Option<Self::Item> {
        let mut rule = Vec::new();
        if Some(self.index) == self.expected {
            return None;
        } else if !self.scanner.has_next() {
            if self.expected.is_none() {
                return None;
            } else {
                panic!("Premature rule line end");
            }
        }
        let is_delete = self.scanner.skip_next("d");
        loop {
            let x = self.scanner.next_isize();
            if x == 0 {
                break;
            } else {
                rule.push(primitives::parse_assig(x));
            }
        }
        self.index += 1;
        let instr = if is_delete {
            RuleInstruction::Del(rule)
        } else {
            RuleInstruction::Add(rule)
        };
        Some(instr)
    }
}

struct RuleReader<L: Iterator>(ProofReader<L>);

impl<Err: Debug, L: Iterator<Item = Result<String, Err>>> Iterator for RuleReader<L> {
    type Item = Vec<Assig>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|x| match x {
            RuleInstruction::Add(rule) => rule,
            RuleInstruction::Del(_) => panic!("Delete rule in program"),
        })
    }
}
