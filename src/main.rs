mod grammar;
mod parser;

use crate::grammar::*;
use crate::parser::{construct_parsing_table, parse};

fn main() {
    let grammar = LL1Grammar::new(vec![
            Variable::new('E'),
            Variable::new('F'),
            Variable::new('T'),
            Variable::new('U'),
            Variable::new('Z')
        ],
        Variable::new('E'),
        vec![
            Rule::new(Variable::new('E'), vec![Symbol::var('T'), Symbol::var('F')]),
            Rule::new(Variable::new('F'), vec![Symbol::ter('+'), Symbol::var('T'), Symbol::var('F')]),
            Rule::new(Variable::new('F'), vec![Symbol::ter('-'), Symbol::var('T'), Symbol::var('F')]),
            Rule::new(Variable::new('F'), vec![Symbol::eps()]),
            Rule::new(Variable::new('T'), vec![Symbol::var('Z'), Symbol::var('U')]),
            Rule::new(Variable::new('U'), vec![Symbol::ter('*'), Symbol::var('Z'), Symbol::var('U')]),
            Rule::new(Variable::new('U'), vec![Symbol::ter('/'), Symbol::var('Z'), Symbol::var('U')]),
            Rule::new(Variable::new('U'), vec![Symbol::eps()]),
            Rule::new(Variable::new('Z'), vec![Symbol::ter('('), Symbol::var('E'), Symbol::ter(')')]),
            Rule::new(Variable::new('Z'), vec![Symbol::ter('1')]),
            Rule::new(Variable::new('Z'), vec![Symbol::ter('x')])
        ]);

    let parsing_table = construct_parsing_table(&grammar);

    let accepted_rules = parse(&grammar, &parsing_table, "1*x+1");

    for rule in accepted_rules.unwrap() {
        println!("{:?}", rule);
    }
}

