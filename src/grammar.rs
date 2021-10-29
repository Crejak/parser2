#[derive(Debug)]
pub struct LL1Grammar {
    non_terminals: Vec<Variable>,
    start_symbol: Variable,
    rules: Vec<Rule>
}

impl LL1Grammar {
    pub fn new(non_terminals: Vec<Variable>, start_symbol: Variable, rules: Vec<Rule>) -> LL1Grammar {
        LL1Grammar {
            non_terminals,
            start_symbol,
            rules
        }
    }

    pub fn non_terminals(&self) -> &[Variable] {
        &self.non_terminals
    }

    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    pub fn start_symbol(&self) -> &Variable {
        &self.start_symbol
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variable {
    name: char
}

impl Variable {
    pub fn new(name: char) -> Self {
        Variable {
            name
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Terminal {
    Character(char),
    Epsilon
}

impl Terminal {
    pub fn new(c: char) -> Self {
        Terminal::Character(c)
    }

    pub fn is_eps(&self) -> bool {
        match self {
            Terminal::Epsilon => true,
            _ => false
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Symbol {
    Variable(Variable),
    Terminal(Terminal)
}

impl Symbol {
    pub fn var(name: char) -> Self {
        Symbol::Variable(Variable::new(name))
    }

    pub fn ter(c: char) -> Self {
        Symbol::Terminal(Terminal::new(c))
    }

    pub fn eps() -> Self {
        Symbol::Terminal(Terminal::Epsilon)
    }

    pub fn is_var(&self) -> bool {
        match self {
            Symbol::Variable(_) => true,
            _ => false
        }
    }

    pub fn is_ter(&self) -> bool {
        match self {
            Symbol::Terminal(_) => true,
            _ => false
        }
    }

    pub fn is_eps(&self) -> bool {
        match self {
            Symbol::Terminal(Terminal::Epsilon) => true,
            _ => false
        }
    }

    pub fn as_var(&self) -> Option<&Variable> {
        match self {
            Symbol::Variable(var) => Some(var),
            _ => None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    left: Variable,
    right: Expression
}

impl Rule {
    pub fn new(left: Variable, right: Expression) -> Rule {
        Rule {
            left,
            right
        }
    }

    pub fn left(&self) -> &Variable {
        &self.left
    }

    pub fn right(&self) -> &Expression {
        &self.right
    }

    pub fn right_is_eps(&self) -> bool {
        self.right.len() == 1
            && self.right.first().unwrap().is_eps()
    }
}

pub type Expression = Vec<Symbol>;