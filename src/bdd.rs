// boolean_expression: a Rust crate for Boolean expressions and BDDs.
//
// Copyright (c) 2016 Chris Fallin <cfallin@c1f.net>. Released under the MIT
// License.
//

use itertools::Itertools;
use std::cmp;
use std::collections::hash_map::Entry as HashEntry;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::fmt::Debug;
use std::hash::Hash;
use std::usize;

use cubes::{Cube, CubeList, CubeVar};
use idd::*;
use Expr;

/// A `BDDFunc` is a function index within a particular `BDD`. It must only
/// be used with the `BDD` instance which produced it.
pub type BDDFunc = usize;

/// A special terminal `BDDFunc` which is constant `false` (zero).
pub const BDD_ZERO: BDDFunc = usize::MAX;
/// A special terminal `BDDFunc` which is constant `true` (one).
pub const BDD_ONE: BDDFunc = usize::MAX - 1;

pub type BDDLabel = usize;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BDDNode {
    pub label: BDDLabel,
    pub lo: BDDFunc,
    pub hi: BDDFunc,
    pub varcount: usize,
}

fn bdd_func_str(b: BDDFunc) -> String {
    if b == BDD_ZERO {
        "ZERO".to_owned()
    } else if b == BDD_ONE {
        "ONE".to_owned()
    } else {
        format!("{}", b)
    }
}

impl fmt::Debug for BDDNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "BDDNode(label = {}, lo = {}, hi = {})",
            self.label,
            bdd_func_str(self.lo),
            bdd_func_str(self.hi)
        )
    }
}

/// A `BDD` is a Binary Decision Diagram, an efficient way to represent a
/// Boolean function in a canonical way. (It is actually a "Reduced Ordered
/// Binary Decision Diagram", which gives it its canonicity assuming terminals
/// are ordered consistently.)
///
/// A BDD is built up from terminals (free variables) and constants, combined
/// with the logical combinators AND, OR, and NOT. It may be evaluated with
/// certain terminal assignments.
///
/// The major advantage of a BDD is that its logical operations are performed,
/// it will "self-simplify": i.e., taking the OR of `And(a, b)` and `And(a,
/// Not(b))` will produce `a` without any further simplification step. Furthermore,
/// the `BDDFunc` representing this value is canonical: if two different
/// expressions are produced within the same BDD and they both result in
/// (simplify down to) `a`, then the `BDDFunc` values will be equal. The
/// tradeoff is that logical operations may be expensive: they are linear in
/// BDD size, but BDDs may have exponential size (relative to terminal count)
/// in the worst case.
#[derive(Clone, Debug)]
pub struct BDD {
    pub nodes: Vec<BDDNode>,
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
        if lo == hi {
            return lo;
        }
        let n = BDDNode {
            label: label,
            lo: lo,
            hi: hi,
            varcount: cmp::min(self.sat_varcount(lo), self.sat_varcount(hi) + 1),
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

    fn sat_varcount(&self, f: BDDFunc) -> usize {
        if f == BDD_ZERO || f == BDD_ONE {
            0
        } else {
            self.nodes[f].varcount
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

    /// Restrict: fundamental building block of logical combinators. Takes a
    /// Shannon cofactor: i.e., returns a new function based on `f` but with the
    /// given label forced to the given value.
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

    /// If-then-else: fundamental building block of logical combinators. Works
    /// by divide-and-conquer: split on the lowest appearing label, take Shannon
    /// cofactors for the two cases, recurse, and recombine with a new node.
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

    pub fn set_minus(&mut self, l: BDDFunc, r: BDDFunc) -> BDDFunc {
        if (l == BDD_ONE || l == BDD_ZERO) && (r == BDD_ONE || r == BDD_ZERO) {
            if l == BDD_ONE && r == BDD_ZERO {
                return BDD_ONE;
            } else {
                return BDD_ZERO;
            }
        }

        let l_lbl = self.min_label(l).unwrap_or(usize::MAX);
        let r_lbl = self.min_label(r).unwrap_or(usize::MAX);

        if l_lbl == r_lbl {
            let l = self.nodes[l].clone();
            let r = self.nodes[r].clone();
            let new_l = self.set_minus(l.lo, r.lo);
            let new_r = self.set_minus(l.hi, r.hi);
            return self.get_node(l_lbl, new_l, new_r);
        } else if l_lbl < r_lbl {
            let l = self.nodes[l].clone();
            let new_l = self.set_minus(l.lo, r);
            let new_r = self.set_minus(l.hi, r);
            return self.get_node(l_lbl, new_l, new_r);
        } else {
            let r = self.nodes[r].clone();
            let new_l = self.set_minus(l, r.lo);
            let new_r = self.set_minus(l, r.hi);
            return self.get_node(r_lbl, new_l, new_r);
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

    pub fn xor(&mut self, a: BDDFunc, b: BDDFunc) -> BDDFunc {
        let not_b = self.not(b);
        self.ite(a, not_b, b)
    }

    pub fn implies(&mut self, a: BDDFunc, b: BDDFunc) -> BDDFunc {
        let not_a = self.not(a);
        self.or(not_a, b)
    }

    pub fn subst(&mut self, f: BDDFunc, map: &[(BDDLabel, BDDLabel)]) -> BDDFunc {
        if f == BDD_ZERO || f == BDD_ONE {
            return f;
        }
        let node = self.nodes[f].clone();
        let new_label = map.iter().find_map(|&(s,t)| if s == node.label { Some(t) } else { None });

        let lo = self.subst(node.lo, map);
        let hi = self.subst(node.hi, map);

        let lbl = match new_label {
            Some(new_label) => new_label,
            _ => node.label
        };

        let fixed = self.fix_ordering(lbl, lo, hi);

        fixed
    }

    fn fix_ordering(&mut self, label: usize, lo: BDDFunc, hi: BDDFunc) -> BDDFunc {
        let lo_lbl = self.min_label(lo).unwrap_or(usize::MAX);
        let hi_lbl = self.min_label(hi).unwrap_or(usize::MAX);

        if label < lo_lbl && label < hi_lbl {
            return self.get_node(label, lo, hi);
        }

        assert!(!(label == lo_lbl  ||  label == hi_lbl));

        if lo_lbl == hi_lbl {
            let l = self.nodes[lo].clone();
            let h = self.nodes[hi].clone();
            let new_lo = self.fix_ordering(label, l.lo, h.lo);
            let new_hi = self.fix_ordering(label, l.hi, h.hi);
            return self.get_node(lo_lbl, new_lo, new_hi);
        } else if lo_lbl < hi_lbl {
            let l = self.nodes[lo].clone();
            let new_lo = self.fix_ordering(label, l.lo, hi);
            let new_hi = self.fix_ordering(label, l.hi, hi);
            return self.get_node(lo_lbl, new_lo, new_hi);
        } else {
            let h = self.nodes[hi].clone();
            let new_lo = self.fix_ordering(label, lo, h.lo);
            let new_hi = self.fix_ordering(label, lo, h.hi);
            return self.get_node(hi_lbl, new_lo, new_hi);
        }
    }

    pub fn raw(&mut self, f: BDDFunc) {
        if f == BDD_ZERO {
            println!("input: ZERO");
        }
        else if f == BDD_ONE {
            println!("input: ONE");
        } else {
            println!("input: {:?}", f);
        }

        if f == BDD_ZERO || f == BDD_ONE {
            println!("done");
            return;
        }
        let node = self.nodes[f].clone();
        println!("node: {:?}", node);

        self.raw(node.lo);
        self.raw(node.hi);

        let lo_lbl = self.min_label(node.lo).unwrap_or(usize::MAX);
        assert!(node.label < lo_lbl);
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
                f = if *val { node.hi } else { node.lo };
            }
        }
        match f {
            BDD_ZERO => Some(false),
            BDD_ONE => Some(true),
            _ => None,
        }
    }

    fn compute_cubelist(&self, memoize_vec: &mut Vec<Option<CubeList>>, n: BDDFunc, nvars: usize) {
        if memoize_vec[n].is_some() {
            return;
        }
        let label = self.nodes[n].label;
        let lo = self.nodes[n].lo;
        let hi = self.nodes[n].hi;
        let lo_list = match lo {
            BDD_ZERO => CubeList::new(),
            BDD_ONE => CubeList::from_list(&[Cube::true_cube(nvars)])
                .with_var(label as usize, CubeVar::False),
            _ => {
                self.compute_cubelist(memoize_vec, lo, nvars);
                memoize_vec[lo]
                    .as_ref()
                    .unwrap()
                    .with_var(label as usize, CubeVar::False)
            }
        };
        let hi_list = match hi {
            BDD_ZERO => CubeList::new(),
            BDD_ONE => CubeList::from_list(&[Cube::true_cube(nvars)])
                .with_var(label as usize, CubeVar::True),
            _ => {
                self.compute_cubelist(memoize_vec, hi, nvars);
                memoize_vec[hi]
                    .as_ref()
                    .unwrap()
                    .with_var(label as usize, CubeVar::True)
            }
        };
        let new_list = lo_list.merge(&hi_list);
        memoize_vec[n] = Some(new_list);
    }

    fn cube_to_expr(&self, c: &Cube) -> Expr<BDDLabel> {
        c.vars()
            .enumerate()
            .flat_map(|(i, v)| match v {
                &CubeVar::False => Some(Expr::not(Expr::Terminal(i))),
                &CubeVar::True => Some(Expr::Terminal(i)),
                &CubeVar::DontCare => None,
            }).fold1(|a, b| Expr::and(a, b))
            .unwrap_or(Expr::Const(true))
    }

    fn cubelist_to_expr(&self, c: &CubeList) -> Expr<BDDLabel> {
        c.cubes()
            .map(|c| self.cube_to_expr(c))
            .fold1(|a, b| Expr::or(a, b))
            .unwrap_or(Expr::Const(false))
    }

    pub fn to_expr(&self, func: BDDFunc, nvars: usize) -> Expr<BDDLabel> {
        if func == BDD_ZERO {
            Expr::Const(false)
        } else if func == BDD_ONE {
            Expr::Const(true)
        } else {
            // At each node, we construct a cubelist, starting from the roots.
            let mut cubelists: Vec<Option<CubeList>> = Vec::with_capacity(self.nodes.len());
            cubelists.resize(self.nodes.len(), None);
            self.compute_cubelist(&mut cubelists, func, nvars);
            self.cubelist_to_expr(cubelists[func].as_ref().unwrap())
        }
    }



    fn compute_cubelist2(&self, memoize_vec: &mut Vec<Option<CubeList>>, n: BDDFunc, nvars: usize) {
        if memoize_vec[n].is_some() {
            return;
        }
        let label = self.nodes[n].label;
        let lo = self.nodes[n].lo;
        let hi = self.nodes[n].hi;
        let lo_list = match lo {
            BDD_ZERO => CubeList::from_list(&[Cube::true_cube(nvars)])
                .with_var(label as usize, CubeVar::True),
            BDD_ONE => CubeList::new(),
            _ => {
                self.compute_cubelist2(memoize_vec, lo, nvars);
                memoize_vec[lo]
                    .as_ref()
                    .unwrap()
                    .with_var(label as usize, CubeVar::True)
            }
        };
        let hi_list = match hi {
            BDD_ZERO => CubeList::from_list(&[Cube::true_cube(nvars)])
                .with_var(label as usize, CubeVar::False),
            BDD_ONE => CubeList::new(),
            _ => {
                self.compute_cubelist2(memoize_vec, hi, nvars);
                memoize_vec[hi]
                    .as_ref()
                    .unwrap()
                    .with_var(label as usize, CubeVar::False)
            }
        };
        let new_list = lo_list.merge(&hi_list);
        memoize_vec[n] = Some(new_list);
    }

    fn cube_to_expr2(&self, c: &Cube) -> Expr<BDDLabel> {
        c.vars()
            .enumerate()
            .flat_map(|(i, v)| match v {
                &CubeVar::False => Some(Expr::not(Expr::Terminal(i))),
                &CubeVar::True => Some(Expr::Terminal(i)),
                &CubeVar::DontCare => None,
            }).fold1(|a, b| Expr::or(a, b))
            .unwrap_or(Expr::Const(true))
    }

    fn print_cube_to_expr2(&self, c: &Cube) -> Vec<Expr<BDDLabel>> {
        c.vars()
            .enumerate()
            .flat_map(|(i, v)| match v {
                &CubeVar::False => Some(Expr::not(Expr::Terminal(i))),
                &CubeVar::True => Some(Expr::Terminal(i)),
                &CubeVar::DontCare => None,
            }).collect()
    }


    fn cubelist_to_expr2(&self, c: &CubeList) -> Expr<BDDLabel> {
        c.cubes()
            .map(|c| self.cube_to_expr2(c))
            .fold1(|a, b| Expr::and(a, b))
            .unwrap_or(Expr::Const(false))
    }

    fn print_cubelist_to_expr2(&self, c: &CubeList) -> Vec<Vec<Expr<BDDLabel>>> {
        c.cubes()
            .map(|c| self.print_cube_to_expr2(c))
            .collect()
//            .unwrap_or(Vec::new())
    }

    pub fn to_expr2(&self, func: BDDFunc, nvars: usize) -> Expr<BDDLabel> {
        if func == BDD_ZERO {
            Expr::Const(false)
        } else if func == BDD_ONE {
            Expr::Const(true)
        } else {
            // At each node, we construct a cubelist, starting from the roots.
            let mut cubelists: Vec<Option<CubeList>> = Vec::with_capacity(self.nodes.len());
            cubelists.resize(self.nodes.len(), None);
            self.compute_cubelist2(&mut cubelists, func, nvars);
            println!("CUBE:\n{:#?}", cubelists[func]);
            let cl = self.print_cubelist_to_expr2(cubelists[func].as_ref().unwrap());
            println!("CUBELIST:\n{:#?}", cl);


            self.cubelist_to_expr2(cubelists[func].as_ref().unwrap())
        }
    }

    pub fn to_max_cubes(&self, func: BDDFunc, nvars: usize) -> CubeList {
        if func == BDD_ZERO {
            CubeList::new()
        } else if func == BDD_ONE {
            CubeList::new()
        } else {
            // At each node, we construct a cubelist, starting from the roots.
            let mut cubelists: Vec<Option<CubeList>> = Vec::with_capacity(self.nodes.len());
            cubelists.resize(self.nodes.len(), None);
            self.compute_cubelist2(&mut cubelists, func, nvars);
            cubelists[func].as_ref().unwrap().clone()
        }
    }

    /// Returns a function that is true whenever the maximum number of
    /// functions in `funcs` are true.
    pub fn max_sat(&mut self, funcs: &[BDDFunc]) -> BDDFunc {
        // First, construct an IDD function for each BDD function,
        // with value 1 if true and 0 if false. Then add these
        // together to obtain a single IDD function whose value is the
        // number of satisfied (true) BDD functions.
        let mut idd = LabelIDD::from_bdd(self);
        let idd_funcs: Vec<_> = funcs.iter().map(|f| idd.from_bdd_func(*f)).collect();
        let satisfied_count = idd_funcs
            .iter()
            .cloned()
            .fold1(|a, b| idd.add(a.clone(), b.clone()))
            .unwrap();

        // Now, find the maximum reachable count.
        let max_count = idd.max_value(satisfied_count.clone());

        // Finally, return a boolean function that is true when the
        // maximal number of functions are satisfied.
        let c = idd.constant(max_count);
        idd.eq(satisfied_count, c, self)
    }

    /// Check whether the function `f` within the BDD is satisfiable.
    pub fn sat(&self, f: BDDFunc) -> bool {
        match f {
            BDD_ZERO => false,
            _ => true,
        }
    }

    /// Produce a function within the BDD representing the given expression
    /// `e`, which may contain ANDs, ORs, NOTs, terminals, and constants.
    pub fn from_expr(&mut self, e: &Expr<BDDLabel>) -> BDDFunc {
        match e {
            &Expr::Terminal(ref t) => self.terminal(t.clone()),
            &Expr::Const(val) => self.constant(val),
            &Expr::Not(ref x) => {
                let xval = self.from_expr(&**x);
                self.not(xval)
            }
            &Expr::And(ref a, ref b) => {
                let aval = self.from_expr(&**a);
                let bval = self.from_expr(&**b);
                self.and(aval, bval)
            }
            &Expr::Or(ref a, ref b) => {
                let aval = self.from_expr(&**a);
                let bval = self.from_expr(&**b);
                self.or(aval, bval)
            }
        }
    }

    /// Compute an assignment for terminals which satisfies 'f'.  If
    /// satisfiable, this function returns a HashMap with the
    /// assignments (true, false) for terminals unless a terminal's
    /// assignment does not matter for satisfiability. If 'f' is not
    /// satisfiable, returns None.
    ///
    /// Example: for the boolean function "a or b", this function
    /// could return one of the following two HashMaps: {"a" -> true}
    /// or {"b" -> true}.
    pub fn sat_one(&self, f: BDDFunc) -> Option<HashMap<BDDLabel, bool>> {
        let mut h = HashMap::new();
        if self.sat_one_internal(f, &mut h) {
            Some(h)
        } else {
            None
        }
    }

    fn sat_one_internal(&self, f: BDDFunc, assignments: &mut HashMap<BDDLabel, bool>) -> bool {
        match f {
            BDD_ZERO => false,
            BDD_ONE => true,
            _ => {
                let hi = self.nodes[f].hi;
                let lo = self.nodes[f].lo;
                if hi != BDD_ZERO
                    && (lo == BDD_ZERO || self.sat_varcount(hi) < self.sat_varcount(lo))
                {
                    assignments.insert(self.nodes[f].label, true);
                    self.sat_one_internal(hi, assignments);
                } else {
                    assignments.insert(self.nodes[f].label, false);
                    self.sat_one_internal(lo, assignments);
                }
                true
            }
        }
    }

}

mod test {
    use super::*;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use Expr;
    extern crate rand;
    use self::rand::Rng;

    fn term_hashmap(vals: &[bool], h: &mut HashMap<u32, bool>) {
        h.clear();
        for (i, v) in vals.iter().enumerate() {
            h.insert(i as u32, *v);
        }
    }

    fn test_bdd(
        b: &BDD,
        f: BDDFunc,
        h: &mut HashMap<u32, bool>,
        inputs: &[bool],
        expected: bool,
    ) {
        term_hashmap(inputs, h);
        assert!(b.evaluate(f, inputs) == Some(expected));
    }

    #[test]
    fn bdd_eval() {
        let mut h = HashMap::new();
        let mut b = BDD::new();
        let expr = Expr::or(
            Expr::and(Expr::Terminal(0), Expr::Terminal(1)),
            Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3))),
        );
        let f = b.from_expr(&expr);
        test_bdd(&b, f, &mut h, &[false, false, true, true], false);
        test_bdd(&b, f, &mut h, &[true, false, true, true], false);
        test_bdd(&b, f, &mut h, &[true, true, true, true], true);
        test_bdd(&b, f, &mut h, &[false, false, false, true], false);
        test_bdd(&b, f, &mut h, &[false, false, false, false], true);
    }

    #[test]
    fn bdd_to_expr() {
        let mut b = BDD::new();
        let f_true = b.constant(true);
        assert!(b.to_expr(f_true, 0) == Expr::Const(true));
        let f_false = b.constant(false);
        assert!(b.to_expr(f_false, 0) == Expr::Const(false));
        let f_0 = b.terminal(0);
        let f_1 = b.terminal(1);
        let f_and = b.and(f_0, f_1);
        assert!(b.to_expr(f_and, 2) == Expr::and(Expr::Terminal(0), Expr::Terminal(1)));
        let f_or = b.or(f_0, f_1);
        assert!(b.to_expr(f_or, 2) == Expr::or(Expr::Terminal(1), Expr::Terminal(0)));
        let f_not = b.not(f_0);
        assert!(b.to_expr(f_not, 2) == Expr::not(Expr::Terminal(0)));
        let f_2 = b.terminal(2);
        let f_1_or_2 = b.or(f_1, f_2);
        let f_0_and_1_or_2 = b.and(f_0, f_1_or_2);
        assert!(
            b.to_expr(f_0_and_1_or_2, 3) == Expr::or(
                Expr::and(Expr::Terminal(0), Expr::Terminal(2)),
                Expr::and(Expr::Terminal(0), Expr::Terminal(1))
            )
        );
    }

    #[test]
    fn bdd_to_expr2() {
        let mut b = BDD::new();
        let f_true = b.constant(true);
        assert!(b.to_expr(f_true, 0) == Expr::Const(true));
        let f_false = b.constant(false);
        assert!(b.to_expr(f_false, 0) == Expr::Const(false));
        let f_0 = b.terminal(0);
        let f_1 = b.terminal(1);
        let f_and = b.and(f_0, f_1);
        assert!(b.to_expr(f_and, 2) == Expr::and(Expr::Terminal(0), Expr::Terminal(1)));
        let f_or = b.or(f_0, f_1);

        let x = b.to_expr2(f_or, 2);
        let xx = b.from_expr(&x);
        assert_eq!(f_or, xx);

        assert!(b.to_expr(f_or, 2) == Expr::or(Expr::Terminal(1), Expr::Terminal(0)));
        let f_not = b.not(f_0);
        assert!(b.to_expr(f_not, 2) == Expr::not(Expr::Terminal(0)));
        let f_2 = b.terminal(2);
        let f_1_or_2 = b.or(f_1, f_2);
        let f_0_and_1_or_2 = b.and(f_0, f_1_or_2);
        assert!(
            b.to_expr(f_0_and_1_or_2, 3) == Expr::or(
                Expr::and(Expr::Terminal(0), Expr::Terminal(2)),
                Expr::and(Expr::Terminal(0), Expr::Terminal(1))
            )
        );

        let x = b.to_expr2(f_0_and_1_or_2, 3);
        let xx = b.from_expr(&x);
        assert_eq!(f_0_and_1_or_2, xx);
        println!("EXPR: {:?}", x);

        assert!(false);
    }

    fn random_expr(r: &mut rand::XorShiftRng, nterminals: usize) -> Expr<BDDLabel> {
        match r.gen_range(0, 5) {
            0 => Expr::Terminal(r.gen_range(0, nterminals) as BDDLabel),
            1 => Expr::Const(r.gen_weighted_bool(2)),
            2 => Expr::Not(Box::new(random_expr(r, nterminals))),
            3 => Expr::And(
                Box::new(random_expr(r, nterminals)),
                Box::new(random_expr(r, nterminals)),
            ),
            4 => Expr::Or(
                Box::new(random_expr(r, nterminals)),
                Box::new(random_expr(r, nterminals)),
            ),
            _ => unreachable!(),
        }
    }

    #[test]
    fn bdd_random_exprs() {
        let mut rng: rand::XorShiftRng = rand::XorShiftRng::new_unseeded();
        let mut b = BDD::new();
        let terminals = 20;
        for _ in 0..100 {
            let expr = random_expr(&mut rng, terminals);
            let expr_b = b.from_expr(&expr);
            let min = b.to_expr(expr_b, terminals);
            let max = b.to_expr2(expr_b, terminals);
            let min_b = b.from_expr(&min);
            let max_b = b.from_expr(&max);
            assert!(expr_b == min_b && min_b == max_b);
        }
    }

    #[test]
    fn sat_one() {
        let mut bdd = BDD::new();

        // empty bdds
        assert!(bdd.sat_one(BDD_ONE).is_some());
        assert!(bdd.sat_one(BDD_ZERO).is_none());

        let a = bdd.terminal(0);
        let b = bdd.terminal(1);
        let b_and_a = bdd.and(a, b);
        let result = bdd.sat_one(b_and_a);
        assert!(result.is_some());
        // assert!(bdd.evaluate(b_and_a, &result.unwrap()));

        let c = bdd.terminal(2);
        let not_c = bdd.not(c);
        let b_and_a_or_not_c = bdd.or(b_and_a, not_c);
        let result = bdd.sat_one(b_and_a_or_not_c);
        assert!(result.is_some());
        // assert!(bdd.evaluate(b_and_a_or_not_c, &result.unwrap()));

        // unsatisfiable formula
        let c_and_not_c = bdd.and(c, not_c);
        assert!(bdd.sat_one(c_and_not_c).is_none());
    }

    #[test]
    fn max_sat() {
        let mut bdd = BDD::new();
        // Test: a, a+b, a+c, c', c, bd, ad, d'
        let a = bdd.terminal(0);
        let b = bdd.terminal(1);
        let c = bdd.terminal(2);
        let d = bdd.terminal(3);
        let cnot = bdd.not(c);
        let dnot = bdd.not(d);
        let ab = bdd.and(a, b);
        let ac = bdd.and(a, c);
        let bd = bdd.and(b, d);
        let ad = bdd.and(a, d);
        let max_sat = bdd.max_sat(&[a, ab, ac, cnot, c, bd, ad, dnot]);
        let abc = bdd.and(ab, c);
        let abcd = bdd.and(abc, d);
        assert!(max_sat == abcd);
    }

    #[test]
    fn max_sat_min_var() {
        let mut bdd = BDD::new();
        // Test: a, a+b, a+c, c', c, bd, d'
        let a = bdd.terminal(0);
        let b = bdd.terminal(1);
        let c = bdd.terminal(2);
        let d = bdd.terminal(3);
        let cnot = bdd.not(c);
        let dnot = bdd.not(d);
        let ab = bdd.and(a, b);
        let ac = bdd.and(a, c);
        let bd = bdd.and(b, d);
        let max_sat = bdd.max_sat(&[a, ab, ac, cnot, c, bd, dnot]);
        let abc = bdd.and(ab, c);
        assert!(max_sat == abc);
        let assn = bdd.sat_one(max_sat).unwrap();
        assert!(assn.get(&0) == Some(&true));
        assert!(assn.get(&1) == Some(&true));
        assert!(assn.get(&2) == Some(&true));
        assert!(assn.get(&3) == None);
    }

    #[test]
    fn test_set_minus() {
        let mut bdd = BDD::new();
        // Test: a, a+b, a+c, c', c, bd, ad, d'
        let a = bdd.terminal(0);
        let b = bdd.terminal(1);
        let c = bdd.terminal(2);
        let d = bdd.terminal(3);

        let ab = bdd.or(a,b);
        let abc = bdd.or(ab,c);
        let abcd = bdd.or(abc,d);


        let cd = bdd.or(c,d);

        let not_c = bdd.not(c);
        let not_d = bdd.not(d);
        let abc_not_d = bdd.and(abc, not_d);

        let minus = bdd.set_minus(abcd, d);
        assert_eq!(minus, abc_not_d);

        let minus1 = bdd.set_minus(abcd, cd);
        let not_c_not_d = bdd.and(not_c, not_d);
        let ab_not_c_not_d = bdd.and(ab, not_c_not_d);
        assert_eq!(minus1, ab_not_c_not_d);
    }

}
