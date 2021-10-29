use std::collections::{HashMap, HashSet};
use crate::grammar::{LL1Grammar, Rule, Symbol, Terminal, Variable};

type NullSet = HashSet<Variable>;

fn construct_null_set(grammar: &LL1Grammar) -> NullSet {
    let mut null_set = HashSet::new();

    let mut has_changed = true;

    while has_changed {
        has_changed = false;

        for rule in grammar.rules() {
            if null_set.contains(rule.left()) {
                continue;
            }

            if rule.right_is_eps() || rule.right().iter().all(|symbol|
                symbol.is_var() && null_set.contains(symbol.as_var().unwrap())) {
                null_set.insert(rule.left().clone());
                has_changed = true;
            }
        }
    }

    null_set
}

type FirstSet = HashMap<Variable, HashSet<Terminal>>;

fn construct_first_set(grammar: &LL1Grammar, null_set: &NullSet) -> FirstSet {
    let mut first_set: FirstSet = grammar.non_terminals()
        .iter()
        .map(|var| (var.clone(), HashSet::<Terminal>::new()))
        .collect();

    let mut has_changed = true;

    while has_changed {
        has_changed = false;

        for variable in grammar.non_terminals() {
            for rule in grammar.rules() {
                if rule.left() != variable {
                    continue;
                }

                for symbol in rule.right() {
                    let (first_of_symbol, should_continue): (HashSet<Terminal>, bool) = match symbol {
                        Symbol::Variable(symbol_var) =>
                            (first_set.get(symbol_var).unwrap().clone(), null_set.contains(symbol_var)),
                        Symbol::Terminal(symbol_ter) =>
                            (HashSet::from([symbol_ter.clone()]), symbol_ter.is_eps()),
                    };

                    let previous_set = first_set.get(variable).unwrap();
                    let previous_size = previous_set.len();
                    let union: HashSet<Terminal> = previous_set.union(&first_of_symbol).map(|s| s.clone()).collect();
                    let new_size = union.len();
                    first_set.insert(variable.clone(), union);
                    if new_size != previous_size {
                        has_changed = true;
                    }

                    if !should_continue {
                        break;
                    }
                }
            }
        }
    }

    first_set
}

fn compute_first_set<'a>(expr: impl Iterator<Item=&'a Symbol>, null_set: &NullSet, first_set: &FirstSet) -> HashSet<Terminal> {
    let mut first_set_of_right = HashSet::new();

    for symbol_after in expr {
        let should_continue = match symbol_after {
            Symbol::Variable(symbol_var) => {
                first_set_of_right = first_set_of_right.union(first_set.get(symbol_var).unwrap()).map(Terminal::clone).collect();
                null_set.contains(symbol_var)
            }
            Symbol::Terminal(symbol_ter) => {
                first_set_of_right.insert(symbol_ter.clone());
                symbol_ter.is_eps()
            }
        };
        if !should_continue {
            break;
        }
    }

    first_set_of_right
}

type FollowSet = HashMap<Variable, HashSet<PTerminal>>;

fn construct_follow_set(grammar: &LL1Grammar, null_set: &NullSet, first_set: &FirstSet) -> FollowSet {
    let mut follow_set: FollowSet = grammar.non_terminals()
        .iter()
        .map(|var| (var.clone(), HashSet::<PTerminal>::new()))
        .collect();

    follow_set.get_mut(grammar.start_symbol()).unwrap().insert(PTerminal::End);

    let mut has_changed = true;

    while has_changed {
        has_changed = false;

        for rule in grammar.rules() {
            for (index, symbol) in rule.right().iter().enumerate() {
                if !symbol.is_var() {
                    continue;
                }

                let mut add_to_follow: HashSet<PTerminal>;

                if index + 1 >= rule.right().len() {
                    add_to_follow = follow_set.get(rule.left()).unwrap().clone();
                } else {
                    let first_set_of_right = compute_first_set(rule.right().iter().skip(index + 1), &null_set, &first_set);

                    add_to_follow = first_set_of_right.iter()
                        .filter(|t| !t.is_eps())
                        .map(|t| PTerminal::from_ter(t).unwrap()).collect();

                    if first_set_of_right.contains(&Terminal::Epsilon) {
                        add_to_follow = add_to_follow.union(follow_set.get(rule.left()).unwrap()).map(PTerminal::clone).collect();
                    }
                }

                let variable = symbol.as_var().unwrap();
                let previous_set = follow_set.get(variable).unwrap();
                let previous_size = previous_set.len();
                let union: HashSet<PTerminal> = previous_set.union(&add_to_follow).map(PTerminal::clone).collect();
                let new_size = union.len();
                follow_set.insert(variable.clone(), union);
                if new_size != previous_size {
                    has_changed = true;
                }
            }
        }
    }

    follow_set
}

type LL1ParsingTable = HashMap<(Variable, PTerminal), Rule>;

fn construct_parsing_table(grammar: &LL1Grammar) -> LL1ParsingTable {
    let mut table = LL1ParsingTable::new();

    let null_set = construct_null_set(&grammar);
    let first_set = construct_first_set(&grammar, &null_set);
    let follow_set = construct_follow_set(&grammar, &null_set, &first_set);

    for rule in grammar.rules() {
        let first_set_of_right = compute_first_set(rule.right().iter(), &null_set, &first_set);

        let mut add_rule_to: HashSet<PTerminal> = first_set_of_right.iter()
            .filter(|t| !t.is_eps())
            .map(|t| PTerminal::from_ter(t).unwrap())
            .collect();

        if first_set_of_right.contains(&Terminal::Epsilon) {
            add_rule_to = add_rule_to.union(follow_set.get(rule.left()).unwrap()).map(PTerminal::clone).collect();
        }

        for p_ter in add_rule_to {
            table.insert((rule.left().clone(), p_ter), rule.clone());
        }
    }

    table
}



#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PTerminal {
    Character(char),
    End
}

impl PTerminal {
    pub fn new(c: char) -> Self {
        PTerminal::Character(c)
    }

    pub fn from_ter(terminal: &Terminal) -> Option<Self> {
        match terminal {
            Terminal::Character(c) => Some(PTerminal::Character(c.clone())),
            Terminal::Epsilon => None
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::{HashMap, HashSet};
    use crate::grammar::*;
    use crate::parser::*;

    fn example_grammar() -> LL1Grammar {
        LL1Grammar::new(vec![
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
            ])
    }

    #[test]
    fn create_null_set() {
        let grammar = example_grammar();

        let null_set = construct_null_set(&grammar);

        assert_eq!(null_set, NullSet::from([Variable::new('F'), Variable::new('U')]));
    }

    #[test]
    fn create_first_set() {
        let grammar = example_grammar();

        let null_set = construct_null_set(&grammar);

        let first_set = construct_first_set(&grammar, &null_set);

        assert_eq!(first_set, FirstSet::from([
            (Variable::new('E'), HashSet::from([Terminal::new('('), Terminal::new('1'), Terminal::new('x')])),
            (Variable::new('T'), HashSet::from([Terminal::new('('), Terminal::new('1'), Terminal::new('x')])),
            (Variable::new('Z'), HashSet::from([Terminal::new('('), Terminal::new('1'), Terminal::new('x')])),
            (Variable::new('F'), HashSet::from([Terminal::new('+'), Terminal::new('-'), Terminal::Epsilon])),
            (Variable::new('U'), HashSet::from([Terminal::new('*'), Terminal::new('/'), Terminal::Epsilon]))
        ]))
    }

    #[test]
    fn create_follow_set() {
        let grammar = example_grammar();

        let null_set = construct_null_set(&grammar);
        let first_set = construct_first_set(&grammar, &null_set);

        let follow_set = construct_follow_set(&grammar, &null_set, &first_set);

        assert_eq!(follow_set, FollowSet::from([
            (Variable::new('E'), HashSet::from([PTerminal::End, PTerminal::new(')')])),
            (Variable::new('F'), HashSet::from([PTerminal::End, PTerminal::new(')')])),
            (Variable::new('T'), HashSet::from([PTerminal::End, PTerminal::new(')'), PTerminal::new('+'), PTerminal::new('-')])),
            (Variable::new('U'), HashSet::from([PTerminal::End, PTerminal::new(')'), PTerminal::new('+'), PTerminal::new('-')])),
            (Variable::new('Z'), HashSet::from([PTerminal::End, PTerminal::new(')'), PTerminal::new('+'), PTerminal::new('-'), PTerminal::new('*'), PTerminal::new('/')])),
        ]))
    }

    #[test]
    fn create_parsing_table() {
        let grammar = example_grammar();

        let parsing_table = construct_parsing_table(&grammar);

        assert_eq!(parsing_table, LL1ParsingTable::from([
            ((Variable::new('E'), PTerminal::new('(')), Rule::new(Variable::new('E'), vec![Symbol::var('T'), Symbol::var('F')])),
            ((Variable::new('E'), PTerminal::new('1')), Rule::new(Variable::new('E'), vec![Symbol::var('T'), Symbol::var('F')])),
            ((Variable::new('E'), PTerminal::new('x')), Rule::new(Variable::new('E'), vec![Symbol::var('T'), Symbol::var('F')])),
            ((Variable::new('F'), PTerminal::new('+')), Rule::new(Variable::new('F'), vec![Symbol::ter('+'), Symbol::var('T'), Symbol::var('F')])),
            ((Variable::new('F'), PTerminal::new('-')), Rule::new(Variable::new('F'), vec![Symbol::ter('-'), Symbol::var('T'), Symbol::var('F')])),
            ((Variable::new('F'), PTerminal::new(')')), Rule::new(Variable::new('F'), vec![Symbol::eps()])),
            ((Variable::new('F'), PTerminal::End), Rule::new(Variable::new('F'), vec![Symbol::eps()])),
            ((Variable::new('T'), PTerminal::new('(')), Rule::new(Variable::new('T'), vec![Symbol::var('Z'), Symbol::var('U')])),
            ((Variable::new('T'), PTerminal::new('1')), Rule::new(Variable::new('T'), vec![Symbol::var('Z'), Symbol::var('U')])),
            ((Variable::new('T'), PTerminal::new('x')), Rule::new(Variable::new('T'), vec![Symbol::var('Z'), Symbol::var('U')])),
            ((Variable::new('U'), PTerminal::new('+')), Rule::new(Variable::new('U'), vec![Symbol::eps()])),
            ((Variable::new('U'), PTerminal::new('-')), Rule::new(Variable::new('U'), vec![Symbol::eps()])),
            ((Variable::new('U'), PTerminal::new('/')), Rule::new(Variable::new('U'), vec![Symbol::ter('/'), Symbol::var('Z'), Symbol::var('U')])),
            ((Variable::new('U'), PTerminal::new('*')), Rule::new(Variable::new('U'), vec![Symbol::ter('*'), Symbol::var('Z'), Symbol::var('U')])),
            ((Variable::new('U'), PTerminal::new(')')), Rule::new(Variable::new('U'), vec![Symbol::eps()])),
            ((Variable::new('U'), PTerminal::End), Rule::new(Variable::new('U'), vec![Symbol::eps()])),
            ((Variable::new('Z'), PTerminal::new('(')), Rule::new(Variable::new('Z'), vec![Symbol::ter('('), Symbol::var('E'), Symbol::ter(')')])),
            ((Variable::new('Z'), PTerminal::new('1')), Rule::new(Variable::new('Z'), vec![Symbol::ter('1')])),
            ((Variable::new('Z'), PTerminal::new('x')), Rule::new(Variable::new('Z'), vec![Symbol::ter('x')]))
        ]));
    }
}