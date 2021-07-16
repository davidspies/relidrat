use std::cmp::Ordering;
use std::fmt::{self, Display, Formatter};
use std::ops::Not;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct Assig(isize);

impl Display for Assig {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Not for Assig {
    type Output = Assig;

    fn not(self) -> Self::Output {
        Assig(-self.0)
    }
}

pub fn parse_assig(x: isize) -> Assig {
    Assig(x)
}

impl PartialOrd for Assig {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Assig {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.0.abs().cmp(&other.0.abs()) {
            Ordering::Equal => self.0.cmp(&other.0),
            res => res,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct RuleIndex(usize);

impl RuleIndex {
    pub fn new(this: usize) -> Self {
        RuleIndex(this)
    }
}

pub fn assignment_line(r: &Vec<Assig>) -> String {
    let mut res = String::new();
    for &Assig(x) in r {
        res.push_str(&format!("{} ", x));
    }
    res.push('0');
    res
}
