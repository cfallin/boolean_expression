boolean\_expression: a small Rust crate for Boolean expressions and BDDs
========================================================================

[![Build Status](https://travis-ci.org/cfallin/boolean_expression.svg?branch=master)](https://travis-ci.org/cfallin/boolean_expression)

This crate provides for the manipulation and evaluation of Boolean expressions
and Binary Decision Diagrams (BDDs), the construction of BDDs from Boolean
expressions, and the construction of Boolean expressions from BDDs (via a
simple cubelist-based minimization algorithm). It also has a very simple
identity-based Boolean expression simplifier, though the cubelist-based
minimizer is more effective.

`boolean_expression` is Copyright (c) 2016 by Chris Fallin &lt;cfallin@c1f.net&gt;
and is released under the MIT license. See `LICENSE` for details.

Documentation: [here](https://docs.rs/boolean_expression/)

Crates.io: [here](https://crates.io/crates/boolean_expression)
