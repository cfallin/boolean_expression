boolean\_expression: a small Rust crate for Boolean expressions and BDDs
========================================================================

This crate provides for the manipulation and evaluation of Boolean expressions
and Binary Decision Diagrams (BDDs), and the construction of BDDs from Boolean
expressions. It also has a very simple Boolean expression simplifier, though
this simplifier does not find minterms (i.e., cancel redundant terms), so
should not be considered complete. This crate may eventually be expanded with
more elaborate simplifiers.

`boolean_expression` is Copyright (c) 2016 by Chris Fallin &lt;cfallin@c1f.net&gt;
and is released under the MIT license. See `LICENSE` for details.

Documentation: [here](https://cfallin.github.io/boolean_expression/boolean_expression/)

Crates.io: [here](https://crates.io/crates/boolean_expression)
