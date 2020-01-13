// boolean_expression: a Rust crate for Boolean expressions and BDDs.
//
// Copyright (c) 2016 Chris Fallin <cfallin@c1f.net>. Released under the MIT
// License.
//

use std::collections::HashMap;
use std::fmt::Debug;
use std::cmp::Ord;
use std::hash::Hash;

/// An `Expr` is a simple Boolean logic expression. It may contain terminals
/// (i.e., free variables), constants, and the following fundamental operations:
/// AND, OR, NOT.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Expr<T>
where
    T: Clone + Debug + Eq + Ord + Hash,
{
    /// A terminal (free variable). This expression node represents a value that
    /// is not known until evaluation time.
    Terminal(T),
    /// A boolean constant: true or false.
    Const(bool),

    /// The logical complement of the contained expression argument.
    Not(Box<Expr<T>>),

    /// The logical AND of the two expression arguments.
    And(Box<Expr<T>>, Box<Expr<T>>),

    /// The logical OR of the two expression arguments.
    Or(Box<Expr<T>>, Box<Expr<T>>),
}

impl<T> Expr<T>
where
    T: Clone + Debug + Eq + Ord + Hash,
{
    /// Returns `true` if this `Expr` is a terminal.
    pub fn is_terminal(&self) -> bool {
        match self {
            &Expr::Terminal(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if this `Expr` is a constant.
    pub fn is_const(&self) -> bool {
        match self {
            &Expr::Const(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if this `Expr` is a NOT node.
    pub fn is_not(&self) -> bool {
        match self {
            &Expr::Not(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if this `Expr` is an AND node.
    pub fn is_and(&self) -> bool {
        match self {
            &Expr::And(_, _) => true,
            _ => false,
        }
    }

    /// Returns `true` if this `Expr` is an OR node.
    pub fn is_or(&self) -> bool {
        match self {
            &Expr::Or(_, _) => true,
            _ => false,
        }
    }

    /// Builds a NOT node around an argument, consuming the argument
    /// expression.
    pub fn not(e: Expr<T>) -> Expr<T> {
        Expr::Not(Box::new(e))
    }

    /// Builds an AND node around two arguments, consuming the argument
    /// expressions.
    pub fn and(e1: Expr<T>, e2: Expr<T>) -> Expr<T> {
        Expr::And(Box::new(e1), Box::new(e2))
    }

    /// Builds an OR node around two arguments, consuming the argument
    /// expressions.
    pub fn or(e1: Expr<T>, e2: Expr<T>) -> Expr<T> {
        Expr::Or(Box::new(e1), Box::new(e2))
    }

    /// Evaluates the expression with a particular set of terminal assignments.
    /// If any terminals are not assigned, they default to `false`.
    pub fn evaluate(&self, vals: &HashMap<T, bool>) -> bool {
        match self {
            &Expr::Terminal(ref t) => *vals.get(t).unwrap_or(&false),
            &Expr::Const(val) => val,
            &Expr::And(ref a, ref b) => a.evaluate(vals) && b.evaluate(vals),
            &Expr::Or(ref a, ref b) => a.evaluate(vals) || b.evaluate(vals),
            &Expr::Not(ref x) => !x.evaluate(vals),
        }
    }

    /// Map terminal values using the specified mapping function.
    pub fn map<F, R>(&self, f: F) -> Expr<R>
    where
        F: Fn(&T) -> R,
        R: Clone + Debug + Eq + Ord + Hash,
    {
        self.map1(&f)
    }

    fn map1<F, R>(&self, f: &F) -> Expr<R>
    where
        F: Fn(&T) -> R,
        R: Clone + Debug + Eq + Ord + Hash,
    {
        match self {
            &Expr::Terminal(ref t) => Expr::Terminal(f(t)),
            &Expr::Const(val) => Expr::Const(val),
            &Expr::Not(ref n) => Expr::not(n.map1(f)),
            &Expr::And(ref a, ref b) => Expr::and(a.map1(f), b.map1(f)),
            &Expr::Or(ref a, ref b) => Expr::or(a.map1(f), b.map1(f)),
        }
    }
}
