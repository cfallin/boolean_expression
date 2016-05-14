pub enum Expr<'a, T> where T: 'a {
    Terminal(T),
    And(&'a Expr<'a>, &'a Expr<'a>),
    Or(&'a Expr<'a>, &'a Expr<'a>),
    Not(&'a Expr<'a>),
    Xor(&'a Expr<'a>),
}

pub struct ExprBox<'a> {
    exprs: Vec<Expr<'a>>,
}

impl ExprBox {
    pub fn new() -> ExprBox {
        ExprBox {
            exprs: Vec::new(),
        }
    }
}
