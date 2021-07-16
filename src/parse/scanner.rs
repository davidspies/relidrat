use std::fmt::Debug;

pub struct Scanner<L: Iterator> {
    line_scanner: L,
    next_tokens: Vec<String>,
}

fn split_tokens(line: String) -> Vec<String> {
    let mut v: Vec<String> = line.split_whitespace().map(|x| x.to_owned()).collect();
    v.reverse();
    v
}

impl<Err: Debug, L: Iterator<Item = Result<String, Err>>> Scanner<L> {
    pub fn new(next_line: String, line_scanner: L) -> Self {
        Scanner {
            line_scanner,
            next_tokens: split_tokens(next_line),
        }
    }

    pub fn next_token(&mut self) -> Option<String> {
        self.peek(|_| ());
        self.next_tokens.pop()
    }

    pub fn next_usize(&mut self) -> usize {
        self.next_token().unwrap().parse::<usize>().unwrap()
    }
    pub fn next_isize(&mut self) -> isize {
        self.next_token().unwrap().parse::<isize>().unwrap()
    }
    pub fn peek<Y>(&mut self, mut f: impl FnMut(&str) -> Y) -> Option<Y> {
        loop {
            let next_line = {
                match self.next_tokens.last() {
                    None => match self.line_scanner.next() {
                        None => return None,
                        Some(nl) => nl.unwrap(),
                    },
                    Some(peeked) => return Some(f(peeked)),
                }
            };
            let next_tokens = split_tokens(next_line);
            self.next_tokens = next_tokens;
        }
    }
    pub fn has_next(&mut self) -> bool {
        self.peek(|_| ()).is_some()
    }
    pub fn skip_next(&mut self, expected: &str) -> bool {
        let result = self.peek(|peeked| peeked == expected).unwrap_or(false);
        if result {
            self.next_tokens.pop();
        }
        result
    }
}
