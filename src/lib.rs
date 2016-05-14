#![allow(unused_imports)]
#![allow(dead_code)]

use std::fmt::Debug;

#[derive(Clone, Debug)]
pub enum Expr<T>
    where T: Clone + Debug + Eq
{
    Terminal(T),
    Const(bool),
    Not(Box<Expr<T>>),
    And(Box<Expr<T>>, Box<Expr<T>>),
    Or(Box<Expr<T>>, Box<Expr<T>>),
}

impl<T> Expr<T>
    where T: Clone + Debug + Eq
{
    pub fn is_terminal(&self) -> bool {
        match self {
            &Expr::Terminal(_) => true,
            _ => false,
        }
    }
    pub fn is_const(&self) -> bool {
        match self {
            &Expr::Const(_) => true,
            _ => false,
        }
    }
    pub fn is_not(&self) -> bool {
        match self {
            &Expr::Not(_) => true,
            _ => false,
        }
    }
    pub fn is_and(&self) -> bool {
        match self {
            &Expr::And(_, _) => true,
            _ => false,
        }
    }
    pub fn is_or(&self) -> bool {
        match self {
            &Expr::Or(_, _) => true,
            _ => false,
        }
    }

    pub fn not(e: Expr<T>) -> Expr<T> {
        Expr::Not(Box::new(e))
    }
    pub fn and(e1: Expr<T>, e2: Expr<T>) -> Expr<T> {
        Expr::And(Box::new(e1), Box::new(e2))
    }
    pub fn or(e1: Expr<T>, e2: Expr<T>) -> Expr<T> {
        Expr::Or(Box::new(e1), Box::new(e2))
    }
}

impl<T> PartialEq for Expr<T> where T: Clone + Debug + Eq {
    fn eq(&self, other: &Expr<T>) -> bool {
        match (self, other) {
            (&Expr::Terminal(ref t1), &Expr::Terminal(ref t2)) => t1.eq(t2),
            (&Expr::Not(ref e1), &Expr::Not(ref t2)) => e1.eq(t2),
            (&Expr::And(ref a1, ref b1), &Expr::And(ref a2, ref b2)) =>
                (a1.eq(a2) && b1.eq(b2)) || (a1.eq(b2) && b1.eq(a2)),
            (&Expr::Or(ref a1, ref b1), &Expr::Or(ref a2, ref b2)) =>
                (a1.eq(a2) && b1.eq(b2)) || (a1.eq(b2) && b1.eq(a2)),
            (&Expr::Const(c1), &Expr::Const(c2)) => c1 == c2,
            _ => false,
        }
    }
}

impl<T> Eq for Expr<T> where T: Clone + Debug + Eq {}

mod simplify;
