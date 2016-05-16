use std::collections::HashMap;
use std::collections::hash_map::Entry as HashEntry;
use std::cmp;
use std::fmt::Debug;
use std::hash::Hash;
use std::usize;

use Expr;

pub type BDDFunc = usize;
pub const BDD_ZERO: BDDFunc = usize::MAX;
pub const BDD_ONE: BDDFunc = usize::MAX - 1;

type BDDLabel = usize;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct BDDNode {
    label: BDDLabel,
    lo: BDDFunc,
    hi: BDDFunc,
}

#[derive(Clone, Debug)]
struct LabelBDD {
    nodes: Vec<BDDNode>,
    dedup_hash: HashMap<BDDNode, BDDFunc>,
}

impl LabelBDD {
    pub fn new() -> LabelBDD {
        LabelBDD {
            nodes: Vec::new(),
            dedup_hash: HashMap::new(),
        }
    }

    fn get_node(&mut self, label: BDDLabel, lo: BDDFunc, hi: BDDFunc) -> BDDFunc {
        let n = BDDNode {
            label: label,
            lo: lo,
            hi: hi,
        };
        match self.dedup_hash.entry(n.clone()) {
            HashEntry::Occupied(o) => *o.get(),
            HashEntry::Vacant(v) => {
                let idx = self.nodes.len() as BDDFunc;
                self.nodes.push(n);
                v.insert(idx);
                idx
            }
        }
    }

    pub fn terminal(&mut self, label: BDDLabel) -> BDDFunc {
        self.get_node(label, BDD_ZERO, BDD_ONE)
    }

    pub fn constant(&mut self, value: bool) -> BDDFunc {
        if value {
            BDD_ONE
        } else {
            BDD_ZERO
        }
    }

    pub fn restrict(&mut self, f: BDDFunc, label: BDDLabel, val: bool) -> BDDFunc {
        if f == BDD_ZERO {
            return BDD_ZERO;
        }
        if f == BDD_ONE {
            return BDD_ONE;
        }

        let node = self.nodes[f].clone();
        if label < node.label {
            f
        } else if label == node.label {
            if val {
                node.hi
            } else {
                node.lo
            }
        } else {
            let lo = self.restrict(node.lo, label, val);
            let hi = self.restrict(node.hi, label, val);
            self.get_node(node.label, lo, hi)
        }
    }

    fn min_label(&self, f: BDDFunc) -> Option<BDDLabel> {
        if f == BDD_ZERO || f == BDD_ONE {
            None
        } else {
            Some(self.nodes[f].label)
        }
    }

    pub fn ite(&mut self, i: BDDFunc, t: BDDFunc, e: BDDFunc) -> BDDFunc {
        if i == BDD_ONE {
            t
        } else if i == BDD_ZERO {
            e
        } else if t == e {
            t
        } else if t == BDD_ONE && e == BDD_ZERO {
            i
        } else {
            let i_var = self.min_label(i).unwrap_or(usize::MAX);
            let t_var = self.min_label(t).unwrap_or(usize::MAX);
            let e_var = self.min_label(e).unwrap_or(usize::MAX);
            let split = cmp::min(i_var, cmp::min(t_var, e_var));
            assert!(split != usize::MAX);
            let i_lo = self.restrict(i, split, false);
            let t_lo = self.restrict(t, split, false);
            let e_lo = self.restrict(e, split, false);
            let i_hi = self.restrict(i, split, true);
            let t_hi = self.restrict(t, split, true);
            let e_hi = self.restrict(e, split, true);
            let lo = self.ite(i_lo, t_lo, e_lo);
            let hi = self.ite(i_hi, t_hi, e_hi);
            self.get_node(split, lo, hi)
        }
    }

    pub fn not(&mut self, n: BDDFunc) -> BDDFunc {
        self.ite(n, BDD_ZERO, BDD_ONE)
    }

    pub fn and(&mut self, a: BDDFunc, b: BDDFunc) -> BDDFunc {
        self.ite(a, b, BDD_ZERO)
    }

    pub fn or(&mut self, a: BDDFunc, b: BDDFunc) -> BDDFunc {
        self.ite(a, BDD_ONE, b)
    }

    pub fn evaluate(&self, func: BDDFunc, inputs: &[bool]) -> Option<bool> {
        let mut f = func;
        for (i, val) in inputs.iter().enumerate() {
            if f == BDD_ZERO || f == BDD_ONE {
                break;
            }
            let node = &self.nodes[f];
            if node.label > i {
                continue;
            } else if node.label == i {
                f = if *val {
                    node.hi
                } else {
                    node.lo
                };
            }
        }
        match f {
            BDD_ZERO => Some(false),
            BDD_ONE => Some(true),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct BDD<T> where T: Clone + Debug + Eq + Ord + Hash {
    bdd: LabelBDD,
    labels: HashMap<T, BDDLabel>,
    next_label: BDDLabel,
}

impl<T> BDD<T> where T: Clone + Debug + Eq + Ord + Hash {
    pub fn new() -> BDD<T> {
        BDD { bdd: LabelBDD::new(), labels: HashMap::new(), next_label: 0 }
    }

    fn label(&mut self, t: T) -> BDDLabel {
        match self.labels.entry(t.clone()) {
            HashEntry::Occupied(o) => *o.get(),
            HashEntry::Vacant(v) => {
                let next_id = self.next_label;
                self.next_label += 1;
                v.insert(next_id);
                next_id
            }
        }
    }

    pub fn terminal(&mut self, t: T) -> BDDFunc {
        let l = self.label(t);
        self.bdd.terminal(l)
    }

    pub fn constant(&mut self, val: bool) -> BDDFunc {
        self.bdd.constant(val)
    }

    pub fn not(&mut self, n: BDDFunc) -> BDDFunc {
        self.bdd.not(n)
    }

    pub fn and(&mut self, a: BDDFunc, b: BDDFunc) -> BDDFunc {
        self.bdd.and(a, b)
    }

    pub fn or(&mut self, a: BDDFunc, b: BDDFunc) -> BDDFunc {
        self.bdd.or(a, b)
    }

    pub fn expr(&mut self, e: &Expr<T>) -> BDDFunc {
        match e {
            &Expr::Terminal(ref t) => {
                self.terminal(t.clone())
            }
            &Expr::Const(val) => self.constant(val),
            &Expr::Not(ref x) => {
                let xval = self.expr(&**x);
                self.not(xval)
            }
            &Expr::And(ref a, ref b) => {
                let aval = self.expr(&**a);
                let bval = self.expr(&**b);
                self.and(aval, bval)
            }
            &Expr::Or(ref a, ref b) => {
                let aval = self.expr(&**a);
                let bval = self.expr(&**b);
                self.or(aval, bval)
            }
        }
    }

    pub fn evaluate(&self, f: BDDFunc, values: &HashMap<T, bool>) -> bool {
        let size = self.next_label;
        let mut valarray = Vec::with_capacity(size);
        valarray.resize(size, false);
        for (t, l) in &self.labels {
            valarray[*l as usize] = *values.get(t).unwrap_or(&false);
        }
        self.bdd.evaluate(f, &valarray).unwrap()
    }
}

mod test {
    use super::*;
    use Expr;
    use std::collections::HashMap;
    extern crate rand;
    use self::rand::Rng;

    fn term_hashmap(vals: &[bool], h: &mut HashMap<u32, bool>) {
        h.clear();
        for (i, v) in vals.iter().enumerate() {
            h.insert(i as u32, *v);
        }
    }

    fn test_bdd(b: &BDD<u32>, f: BDDFunc, h: &mut HashMap<u32, bool>, inputs: &[bool], expected: bool) {
        term_hashmap(inputs, h);
        assert!(b.evaluate(f, h) == expected);
    }

    #[test]
    fn bdd_eval() {
        let mut h = HashMap::new();
        let mut b = BDD::new();
        let expr = Expr::or(Expr::and(Expr::Terminal(0), Expr::Terminal(1)),
                            Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3))));
        let f = b.expr(&expr);
        test_bdd(&b, f, &mut h, &[false, false, true, true], false);
        test_bdd(&b, f, &mut h, &[true, false, true, true], false);
        test_bdd(&b, f, &mut h, &[true, true, true, true], true);
        test_bdd(&b, f, &mut h, &[false, false, false, true], false);
        test_bdd(&b, f, &mut h, &[false, false, false, false], true);
    }

    fn bits_to_hashmap(bits: usize, n: usize, h: &mut HashMap<u32, bool>) {
        for b in 0..bits {
            h.insert(b as u32, (n & (1 << b)) != 0);
        }
    }

    fn test_bdd_expr(e: Expr<u32>, nterminals: usize) {
        let mut b = BDD::new();
        let f = b.expr(&e);
        let mut terminal_values = HashMap::new();
        for v in 0..(1 << nterminals) {
            bits_to_hashmap(nterminals, v, &mut terminal_values);
            let expr_val = e.evaluate(&terminal_values);
            let bdd_val = b.evaluate(f, &terminal_values);
            assert!(expr_val == bdd_val);
        }
    }

    fn random_expr(r: &mut rand::XorShiftRng, nterminals: usize) -> Expr<u32> {
        match r.gen_range(0, 5) {
            0 => Expr::Terminal(r.gen_range(0, nterminals) as u32),
            1 => Expr::Const(r.gen_weighted_bool(2)),
            2 => Expr::Not(Box::new(random_expr(r, nterminals))),
            3 => {
                Expr::And(Box::new(random_expr(r, nterminals)),
                          Box::new(random_expr(r, nterminals)))
            }
            4 => {
                Expr::Or(Box::new(random_expr(r, nterminals)),
                         Box::new(random_expr(r, nterminals)))
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn bdd_exhaustive_exprs() {
        let mut rng: rand::XorShiftRng = rand::XorShiftRng::new_unseeded();
        for _ in 0..100 {
            let expr = random_expr(&mut rng, 6);
            test_bdd_expr(expr, 6);
        }
    }
}
