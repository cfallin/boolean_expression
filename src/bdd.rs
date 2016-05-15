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

pub type BDDLabel = usize;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BDDNode {
    label: BDDLabel,
    lo: BDDFunc,
    hi: BDDFunc,
}

#[derive(Clone, Debug)]
pub struct BDD {
    nodes: Vec<BDDNode>,
    dedup_hash: HashMap<BDDNode, BDDFunc>,
}

impl BDD {
    pub fn new() -> BDD {
        BDD {
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

pub struct BDDExprBuilder<T>
    where T: Clone + Debug + Eq + Ord + Hash
{
    bdd: BDD,
    label_map: HashMap<T, BDDLabel>,
    next_label: BDDLabel,
}

impl<T> BDDExprBuilder<T>
    where T: Clone + Debug + Eq + Ord + Hash
{
    pub fn new() -> BDDExprBuilder<T> {
        BDDExprBuilder {
            bdd: BDD::new(),
            label_map: HashMap::new(),
            next_label: 0,
        }
    }

    fn label_mut(&mut self, t: &T) -> BDDLabel {
        match self.label_map.entry(t.clone()) {
            HashEntry::Occupied(o) => *o.get(),
            HashEntry::Vacant(v) => {
                let new_id = self.next_label;
                self.next_label += 1;
                v.insert(new_id);
                new_id
            }
        }
    }

    pub fn label(&self, t: &T) -> Option<BDDLabel> {
        self.label_map.get(t).map(|l| *l)
    }

    pub fn build(&mut self, e: &Expr<T>) -> BDDFunc {
        match e {
            &Expr::Terminal(ref t) => {
                let l = self.label_mut(t);
                self.bdd.terminal(l)
            }
            &Expr::Const(val) => self.bdd.constant(val),
            &Expr::Not(ref x) => {
                let xval = self.build(&**x);
                self.bdd.not(xval)
            }
            &Expr::And(ref a, ref b) => {
                let aval = self.build(&**a);
                let bval = self.build(&**b);
                self.bdd.and(aval, bval)
            }
            &Expr::Or(ref a, ref b) => {
                let aval = self.build(&**a);
                let bval = self.build(&**b);
                self.bdd.or(aval, bval)
            }
        }
    }

    pub fn bdd(&self) -> &BDD {
        &self.bdd
    }
    pub fn bdd_mut(&mut self) -> &mut BDD {
        &mut self.bdd
    }
    pub fn take(self) -> BDD {
        self.bdd
    }
}

mod test {
    use super::*;
    use Expr;
    use std::collections::HashMap;
    extern crate rand;
    use self::rand::Rng;

    #[test]
    fn bdd_eval() {
        let mut b = BDDExprBuilder::new();
        let expr = Expr::or(Expr::and(Expr::Terminal(1), Expr::Terminal(2)),
                            Expr::and(Expr::not(Expr::Terminal(3)), Expr::not(Expr::Terminal(4))));
        let f = b.build(&expr);
        let bdd = b.take();
        assert!(bdd.evaluate(f, &[false, false, true, true]) == Some(false));
        assert!(bdd.evaluate(f, &[true, false, true, true]) == Some(false));
        assert!(bdd.evaluate(f, &[true, true, true, true]) == Some(true));
        assert!(bdd.evaluate(f, &[false, false, false, true]) == Some(false));
        assert!(bdd.evaluate(f, &[false, false, false, false]) == Some(true));
    }

    fn bits_to_hashmap(bits: usize, n: usize, h: &mut HashMap<u32, bool>) {
        for b in 0..bits {
            h.insert(b as u32, (n & (1 << b)) != 0);
        }
    }

    fn test_bdd_expr(e: Expr<u32>, nterminals: usize) {
        let mut b = BDDExprBuilder::<u32>::new();
        let f = b.build(&e.clone());
        // This is a little roundabout:
        // - the expression evaluation expects a hashmap from arbitrary terminal type T to terminal values.
        // - the BDD evaluation expects a vector of label values indexed by BDD variable labels.
        // - we can map from the former to the latter by going through the BDD builder.
        //
        // TODO: clean this up: include a terminal-to-label map in the BDD itself.
        let mut terminal_values = HashMap::new();
        let mut label_values = vec![false; nterminals];
        let terminal_to_label: Vec<Option<BDDLabel>> = (0..(nterminals as u32))
                                                           .map(|i| b.label(&i))
                                                           .collect();
        let bdd = b.take();
        for v in 0..(1 << nterminals) {
            bits_to_hashmap(nterminals, v, &mut terminal_values);
            for i in 0..(nterminals as u32) {
                if let Some(l) = terminal_to_label[i as usize] {
                    label_values[l] = *terminal_values.get(&i).unwrap();
                }
            }
            let expr_val = e.evaluate(&terminal_values);
            let bdd_val = bdd.evaluate(f, &label_values).unwrap();
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
