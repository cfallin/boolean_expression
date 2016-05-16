// boolean_expression: a Rust crate for Boolean expressions and BDDs.
//
// Copyright (c) 2016 Chris Fallin <cfallin@c1f.net>. Released under the MIT
// License.
//

#![allow(unused_imports)]
#![allow(dead_code)]

//! # boolean\_expression expression manipulation / BDD library
//!
//! This crate provides for the manipulation and evaluation of Boolean expressions
//! and Binary Decision Diagrams (BDDs), and the construction of BDDs from Boolean
//! expressions. It also has a very simple Boolean expression simplifier, though
//! this simplifier does not find minterms (i.e., cancel redundant terms), so
//! should not be considered complete. This crate may eventually be expanded with
//! more elaborate simplifiers.

mod expr;
mod bdd;
mod simplify;

pub use expr::*;
pub use bdd::*;
