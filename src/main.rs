#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(bindings_after_at)]
#![feature(or_patterns)]

use {
    std::{
        collections::HashMap,
        ops::DerefMut,
    },
};

#[derive(Debug)]
pub enum Error {
    UndefinedVar(char),
    FailedReduction(u64),
}

type Result<T> = std::result::Result<T, Error>;

pub trait Env {
    fn value_of(&self, key: char) -> Option<Expr>;
}

impl Env for HashMap<char, bool> {
    fn value_of(&self, c : char) -> Option<Expr> {
        self.get(&c).map(|b| (*b).into())
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Theorem {
    Id,
    Null,
    Idempotent,
    Involve,
    Complement,
    Commute,
    Associate,
    Distribute,
    Cover,
    Combine,
    Concensus,
    DeMorgan,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Zero,
    One,
    Var(char),

    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),

}

impl From<bool> for Expr {
    fn from(b : bool) -> Expr {
        if b {
            Expr::One
        } else {
            Expr::Zero
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f : &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Not(a) => {
                match **a {
                    Expr::Not(_) |
                    Expr::Var(_) |
                    Expr::One |
                    Expr::Zero => {
                        write!(f, "{}'", a)
                    },
                    _ => {
                        write!(f, "({})'", a)
                    }
                }
            },
            Expr::And(a, b) => {
                match **a {
                    Expr::Or(_, _) => write!(f, "({})", a)?,
                    _ => write!(f, "{}", a)?,
                };

                match **b {
                    Expr::Or(_, _) => write!(f, "({})", b)?,
                    _ => write!(f, "{}", b)?,
                };

                Ok(())
            },
            Expr::Or(a, b) => {
                write!(f, "{}+{}", a, b)
            },
            Expr::One => write!(f, "1"),
            Expr::Zero => write!(f, "0"),
            Expr::Var(c) => write!(f, "{}", c),
        }
    }
}



impl Expr {
    fn boxed(self) -> Box<Self> {
        Box::new(self)
    }

    fn vars(&self, v : &mut Vec<char>) {
        match self {
            Expr::Not(a) => a.vars(v),
            Expr::And(a, b) => {
                a.vars(v);
                b.vars(v);
            },
            Expr::Or(a, b) => {
                a.vars(v);
                b.vars(v);
            },
            Expr::Var(c) => {
                v.push(*c);
            },
            _ => {},
        }
    }

    pub fn table(&self) -> Table {
        Table {
            expr: self,
        }
    }


    pub fn reduce(&mut self, thm : Theorem, skip : u64) -> Result<()> {

        if  matches!(self, Expr::Var(_) | Expr::One | Expr::Zero) {
            return Err(Error::FailedReduction(skip))
        }

        macro_rules! swap {
            ($dest:ident,$src:ident) => {
                {
                    let mut xx = Expr::Zero;

                    std::mem::swap(&mut xx, $src.deref_mut());
                    std::mem::replace($dest, xx);
                }
            };
        }

        macro_rules! force_match {
            ($p:pat,$v:expr,$b:block) => {
                if let $p = $v {
                    $b
                } else {
                    unreachable!()
                }
            };
        }

        macro_rules! recurse_skip {
            ($first:ident) => {
                $first.reduce(thm, skip-1)
            };
            ($first:ident,$($rest:ident),*) => {
                $first.reduce(thm, skip-1)
                    $(
                        .or_else(|err| {
                            if let Error::FailedReduction(skip) = err {
                                $rest.reduce(thm, skip)
                            } else {
                                Err(err)
                            }
                        })
                    )*
            };
        }

        match thm {
            Theorem::Id => {
                match self {
                    Expr::And(box Expr::One, x) |
                    Expr::And(x, box Expr::One) |
                    Expr::Or(box Expr::Zero, x) |
                    Expr::Or(x, box Expr::Zero) => {
                        return if skip == 0 {
                            swap!(self, x);
                            Ok(())
                        } else {
                            recurse_skip!(x)
                        }
                    },
                    _ => {},
                }
            },
            Theorem::Null => {
                match self {
                    Expr::And(x @ box Expr::Zero, _) |
                    Expr::And(_, x @ box Expr::Zero) |
                    Expr::Or(x @ box Expr::One, _) |
                    Expr::Or(_, x @ box Expr::One) => {
                        return if skip == 0 {
                            swap!(self, x);
                            Ok(())
                        } else {
                            recurse_skip!(x)
                        }
                    },
                    _ => {},
                }
            },
            Theorem::Idempotent => {
                match self {
                    Expr::And(x, y) |
                    Expr::Or(x, y) => {
                        if x == y {
                            return if skip == 0 {
                                swap!(self, x);
                                Ok(())
                            } else {
                                x.reduce(thm, skip-1)
                            }
                        }
                    }
                    _ => {},
                }
            },
            Theorem::Involve => {
                match self {
                    Expr::Not(box Expr::Not(x)) => {
                        return if skip == 0 {
                            swap!(self, x);
                            Ok(())
                        } else {
                            force_match!(Expr::Not(x), self, {
                                recurse_skip!(x)
                            })
                        }
                    },
                    _ => {},
                }
            },
            Theorem::Complement => {
                match self {
                    Expr::And(box Expr::Not(x), y) |
                    Expr::And(x, box Expr::Not(y)) if x == y => {
                        return if skip == 0 {
                            std::mem::replace(self, Expr::Zero);
                            Ok(())
                        } else {
                            recurse_skip!(x, y)
                        }
                    },
                    Expr::And(x @ box Expr::One, y @ box Expr::Zero) |
                    Expr::And(x @ box Expr::Zero, y @ box Expr::One) => {
                        return if skip == 0 {
                            std::mem::replace(self, Expr::Zero);
                            Ok(())
                        } else {
                            return Err(Error::FailedReduction(skip))
                        }
                    },
                    Expr::Or(box Expr::Not(x), y) |
                    Expr::Or(x, box Expr::Not(y)) if x == y => {
                        return if skip == 0 {
                            std::mem::replace(self, Expr::One);
                            Ok(())
                        } else {
                            recurse_skip!(x, y)
                        }
                    },
                    Expr::Or(box Expr::One, box Expr::Zero) |
                    Expr::Or(box Expr::Zero, box Expr::One) => {
                        return if skip == 0 {
                            std::mem::replace(self, Expr::One);
                            Ok(())
                        } else {
                            return Err(Error::FailedReduction(skip))
                        }
                    },
                    _ => {},
                }
            },
            Theorem::Commute => {
                match self {
                    Expr::Or(x, y) |
                    Expr::And(x, y) => {
                        return if skip == 0 {
                            std::mem::swap(x, y);
                            Ok(())
                        } else {
                            recurse_skip!(x, y)
                        }
                    }
                    _ => {},
                }
            },
            Theorem::Associate => {
                match self {
                    // (xy)z
                    // z(xy)
                    // z(yx)
                    // x(yz)
                    Expr::Or(r @ box Expr::Or(_, _), z) |
                    Expr::And(r @ box Expr::And(_, _), z) => {
                        return if skip == 0 {
                            let mut zz = box Expr::One;

                            std::mem::swap(z, &mut zz);
                            std::mem::swap(z, r);

                            force_match!(
                                (box Expr::Or(x, y) | box Expr::And(x, y)),
                                z,
                                {
                                    std::mem::swap(x, y);
                                    std::mem::swap(y, &mut zz);
                                }
                            );

                            std::mem::swap(&mut zz, r);

                            Ok(())
                        } else {
                            recurse_skip!(r, z)
                        }
                    },
                    // x(yz)
                    // (yz)x
                    // (zy)x
                    // (xy)z
                    Expr::Or(x, r @ box Expr::Or(_, _)) |
                    Expr::And(x, r @ box Expr::And(_, _)) => {
                        return if skip == 0 {
                            let mut xx = box Expr::One;

                            std::mem::swap(x, &mut xx);
                            std::mem::swap(x, r);

                            force_match!(
                                (box Expr::Or(y, z) | box Expr::And(y, z)),
                                x,
                                {
                                    std::mem::swap(y, z);
                                    std::mem::swap(y, &mut xx);
                                }
                            );

                            std::mem::swap(&mut xx, r);

                            Ok(())
                        } else {
                            recurse_skip!(x, r)
                        }
                    },
                    _ => {},
                }
            },
            Theorem::Distribute => {

                match self {
                    Expr::And(
                        box Expr::Or(a, b),
                        box Expr::Or(c, d),
                    ) if a == c || a == d || b == c || b == d => {
                        return if skip == 0 {
                            let mut ret = Expr::Or(
                                box Expr::One,
                                box Expr::And(
                                    box Expr::One,
                                    box Expr::One,
                                ),
                            );

                            // a * (b + c)
                            let (a, b, c) =
                                if a == c {
                                    (a, b, d)
                                } else if a == d {
                                    (a, b, c)
                                } else if b == c {
                                    (b, a, d)
                                } else if b == d {
                                    (b, a, c)
                                } else {
                                    unreachable!()
                                };


                            force_match!(
                                Expr::Or(box aa, box Expr::And(bb, cc)),
                                &mut ret,
                                {
                                    std::mem::swap(aa, a);
                                    std::mem::swap(bb, b);
                                    std::mem::swap(cc, c);
                                }
                            );

                            std::mem::swap(self, &mut ret);

                            Ok(())
                        } else {
                            recurse_skip!(a, b, c, d)
                        }
                    },
                    Expr::Or(
                        box Expr::And(a, b),
                        box Expr::And(c, d),
                    ) if a == c || a == d || b == c || b == d => {
                        return if skip == 0 {
                            let mut ret = Expr::And(
                                box Expr::One,
                                box Expr::Or(
                                    box Expr::One,
                                    box Expr::One,
                                ),
                            );

                            // a * (b + c)
                            let (a, b, c) =
                                if a == c {
                                    (a, b, d)
                                } else if a == d {
                                    (a, b, c)
                                } else if b == c {
                                    (b, a, d)
                                } else if b == d {
                                    (b, a, c)
                                } else {
                                    unreachable!()
                                };


                            force_match!(
                                Expr::And(box aa, box Expr::Or(bb, cc)),
                                &mut ret,
                                {
                                    std::mem::swap(aa, a);
                                    std::mem::swap(bb, b);
                                    std::mem::swap(cc, c);
                                }
                            );

                            std::mem::swap(self, &mut ret);

                            Ok(())
                        } else {
                            recurse_skip!(a, b, c, d)
                        }
                    },
                    _ => {},
                }
            },
            _ => unimplemented!(),
        };

        // recurse further if no matches found
        match self {
            Expr::Not(x) => {
                x.reduce(thm, skip)
            },
            Expr::Or(x, y) |
            Expr::And(x, y) => {
                x.reduce(thm, skip)
                    .or_else(|err| {
                        if let Error::FailedReduction(skip) = err {
                            y.reduce(thm, skip)
                        } else {
                            Err(err)
                        }
                    })
            },
            _ => unreachable!(),
        }
    }


    pub fn eval<E : Env>(&self, env : &E) -> Result<bool> {
        match self {
            Expr::Not(a) => a.eval(env).map(|x| !x),
            Expr::And(a, b) => {
                let aa = a.eval(env)?;
                let bb = b.eval(env)?;
                Ok(aa && bb)
            },
            Expr::Or(a, b) => {
                let aa = a.eval(env)?;
                let bb = b.eval(env)?;
                Ok(aa || bb)
            },
            Expr::Var(c) => {
                env
                    .value_of(*c)
                    .ok_or(Error::UndefinedVar(*c))
                    .and_then(|a| a.eval(env))
            },
            Expr::One => Ok(true),
            Expr::Zero => Ok(false),
        }
    }
}

pub struct Table<'a> {
    expr : &'a Expr,
}

impl<'a> Table<'a> {
    fn iter(&self) -> TableIter<'a> {
        let mut vars = Vec::new();
        self.expr.vars(&mut vars);
        vars.sort_unstable();

        let mut vals = Vec::new();
        vals.resize(vars.len(), false);

        TableIter {
            expr : self.expr,
            vars : vars,
            vals : vals,
            not_first : false,
        }

    }
}

impl Eq for Table<'_> {}

impl PartialEq for Table<'_> {
    fn eq(&self, other : &Self) -> bool {
        let mut t1 = self.iter();
        let mut t2 = other.iter();

        if t1.vars != t2.vars {
            return false;
        }

        loop {
            let v1 = t1.next();
            let v2 = t2.next();

            if let Some((_, b1)) = v1 {
                if let Some((_, b2)) = v2 {
                    if b1 != b2 {
                        return false;
                    }
                } else {
                    return false;
                }
            } else {
                return v2.is_none();
            }
        }
    }
}

impl<'a> std::fmt::Display for Table<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {

        let mut table = self.iter();

        for var in &table.vars {
            write!(f, "{} | ", var)?;
        }
        let expr_str = format!("{}", self.expr);

        writeln!(f, "{}", expr_str)?;

        for _ in &table.vars {
            write!(f, "----")?;
        }

        write!(f, "{}", "-".repeat(expr_str.len()))?;

        while let Some((row, out)) = table.next() {
            writeln!(f)?;

            for val in row {
                write!(f, "{} | ", if *val { 1 } else { 0 })?;
            }

            write!(f, "{}",
                if out {
                    1
                } else {
                    0
                })?;
        }

        Ok(())
    }
}

struct ParallelEnv<'a> {
    key : &'a [char], // must be sorted
    val : &'a [bool],
}

impl<'a> Env for ParallelEnv<'a> {
    fn value_of(&self, c : char) -> Option<Expr> {
        self.key
            .binary_search(&c)
            .map(|i| self.val[i].into())
            .ok()
    }
}

struct TableIter<'a> {
    expr : &'a Expr,
    vars : Vec<char>,
    vals : Vec<bool>,
    not_first : bool,
}


impl<'a> TableIter <'a> {
    fn env(&self) -> ParallelEnv {
        ParallelEnv{
            key : self.vars.as_slice(),
            val : self.vals.as_slice(),
        }
    }


    // streaming iterator
    fn next(&mut self) -> Option<(&[bool], bool)> {

        if !self.not_first {
            self.not_first = true;
            return Some((
                self.vals.as_slice(),
                self.expr.eval(&self.env()).unwrap(),
            ))
        }

        for val in self.vals.iter_mut().rev() {
            if *val == false {
                *val = true;
                return Some((
                    self.vals.as_slice(),
                    self.expr.eval(&self.env()).unwrap(),
                    ));
            } else {
                *val = false;
            }
        }

        None
    }
}


mod dsl {
    #![allow(dead_code)]
    use super::*;


    pub const one : Expr = Expr::One;
    pub const zero : Expr = Expr::Zero;

    pub fn var(c : char) -> Expr {
        Expr::Var(c)
    }

    pub fn not(a : Expr) -> Expr {
        Expr::Not(box a)
    }

    pub fn and(a : Expr, b : Expr) -> Expr {
        Expr::And(box a, box b)
    }

    pub fn or(a : Expr, b : Expr) -> Expr {
        Expr::Or(box a, box b)
    }
}




fn main() {
    let expr = Expr::And(
        Expr::Var('C').boxed(),
        //Expr::Not(
            Expr::Or(
                Expr::Var('B').boxed(),
                Expr::Var('A').boxed(),
            ).boxed(),
        //).boxed(),
    );

    let expr = Expr::Not(
        Expr::Not(
            Expr::And(
                Expr::Var('B').boxed(),
                Expr::Var('A').boxed(),
            ).boxed(),
        ).boxed(),
    );

    let mut env = HashMap::new();
    env.insert('A', false);
    env.insert('B', false);

    println!("{:?}", expr.eval(&env));

    let mut v = Vec::new();
    expr.vars(&mut v);
    println!("{:?}", v);

    println!("{}", expr.table());

    let a = Expr::Not(
        Expr::Not(
            Expr::And(
                Expr::Var('A').boxed(),
                Expr::Var('B').boxed(),
            ).boxed(),
        ).boxed(),
    );

    let b = Expr::And(
        Expr::Var('A').boxed(),
        Expr::Var('B').boxed(),
    );

    println!("a: {}", a);
    println!("b: {}", b);

    println!("{} =expr= {} => {}", a, b, a == b);
    println!("{} =table= {} => {}", a, b, a.table() == b.table());
}

mod tests {
    use super::*;
    use super::dsl::*;

    #[test]
    fn test_expr_eq() {
        let tcases = vec![
            (one, one, true),
            (zero, one, false),
            (zero, zero, true),
            (var('A'), one, false),
            (var('A'), var('B'), false),
            (var('A'), var('A'), true),
            (not(one), not(zero), false),
            (not(not(one)), not(zero), false),
            (not(one), not(one), true),
            (
                and(zero, zero),
                and(zero, zero),
                true,
            ),
            (
                and(zero, zero),
                and(zero, one),
                false,
            ),
            (
                or(zero, zero),
                or(zero, zero),
                true,
            ),
            (
                or(zero, zero),
                or(zero, one),
                false,
            ),
        ];

        for tcase in tcases {
            assert_eq!(tcase.0 == tcase.1, tcase.2,
                       "{} == {}", tcase.0, tcase.1);
        }
    }

    #[test]
    fn test_table_eq() {
        let tcases = vec![
            (one, one, true),
            (zero, zero, true),
            (one, zero, false),
            (zero, one, false),
            (
                and(var('A'), var('B')),
                and(var('A'), var('A')),
                false,
            ),
            (
                and(var('A'), var('B')),
                and(var('A'), var('C')),
                false,
            ),
            (
                and(var('A'), var('B')),
                and(var('B'), var('A')),
                true,
            ),
            (
                or(var('A'), var('B')),
                or(var('A'), var('B')),
                true,
            ),
            (
                or(var('A'), var('B')),
                or(var('A'), var('B')),
                true,
            ),
            (
                not(not(or(var('A'), var('B')))),
                or(var('A'), var('B')),
                true,
            ),
            (
                not(or(var('A'), var('B'))),
                and(not(var('A')), not(var('B'))),
                true,
            ),
        ];

        for tcase in tcases {
            assert_eq!(tcase.0.table() == tcase.1.table(), tcase.2,
                       "{} == {}", tcase.0, tcase.1);
        }
    }



    #[test]
    fn test_reduction_id() {
        let tcases = vec![
            (
                or(one, zero),
                0,
                Some(one),
            ),
            (
                or(zero, var('A')),
                0,
                Some(var('A')),
            ),
            (
                or(one, one),
                0,
                None,
            ),
            (
                and(one, one),
                0,
                Some(one),
            ),
            (
                and(var('A'), one),
                0,
                Some(var('A')),
            ),
            (
                and(var('A'), one),
                1,
                None,
            ),
            (
                or(and(var('A'), one), one),
                0,
                Some(or(var('A'), one)),
            ),
            (
                or(
                    and(var('A'), one),
                    and(var('B'), one)
                ),
                1,
                Some(
                    or(
                        and(var('A'), one),
                        var('B')
                    )
                ),
            ),
            (
                and(
                    or(var('A'), zero),
                    or(var('B'), zero)
                ),
                1,
                Some(
                    and(
                        or(var('A'), zero),
                        var('B')
                    )
                ),
            ),
        ];

        for tcase in tcases {
            let mut got = tcase.0.clone();
            let res = got.reduce(Theorem::Id, tcase.1);

            if let Some(expect) = tcase.2 {
                assert!(res.is_ok() && got == expect,
                    "({} => {:?}) == {:?} {}",
                    tcase.0,
                    got,
                    expect,
                    if res.is_ok() { "ok" } else { "not ok" });

            } else {
                assert!(
                    res.is_err() && got == tcase.0,
                    "did not apply id thm")

            }
        }
    }

    #[test]
    fn test_reduction_null() {
        let tcases = vec![
            (
                or(one, zero),
                0,
                Some(one),
            ),
            (
                or(one, var('A')),
                0,
                Some(one),
            ),
            (
                or(zero, zero),
                0,
                None,
            ),
            (
                and(zero, one),
                0,
                Some(zero),
            ),
            (
                and(var('A'), zero),
                0,
                Some(zero),
            ),
            (
                and(var('A'), zero),
                1,
                None,
            ),
            (
                or(and(var('A'), zero), zero),
                0,
                Some(or(zero, zero)),
            ),
            (
                or(
                    and(var('A'), zero),
                    and(var('B'), zero)
                ),
                1,
                Some(
                    or(
                        and(var('A'), zero),
                        zero
                    )
                ),
            ),
            (
                and(
                    or(var('A'), one),
                    or(var('B'), one)
                ),
                1,
                Some(
                    and(
                        or(var('A'), one),
                        one
                    )
                ),
            ),
        ];

        for tcase in tcases {
            let mut got = tcase.0.clone();
            let res = got.reduce(Theorem::Null, tcase.1);

            if let Some(expect) = tcase.2 {
                assert!(res.is_ok() && got == expect,
                    "({} => {:?}) == {:?} {}",
                    tcase.0,
                    got,
                    expect,
                    if res.is_ok() { "ok" } else { "not ok" });

            } else {
                assert!(
                    res.is_err() && got == tcase.0,
                    "did not apply null thm")

            }
        }
    }

    #[test]
    fn test_reduction_idempotent() {
        let tcases = vec![
            (
                or(one, one),
                0,
                Some(one),
            ),
            (
                or(var('A'), var('A')),
                0,
                Some(var('A')),
            ),
            (
                or(var('A'), var('B')),
                0,
                None,
            ),
            (
                and(var('A'), var('A')),
                0,
                Some(var('A')),
            ),
            (
                and(var('A'), var('B')),
                0,
                None,
            ),
            (
                and(
                    or(var('A'), var('A')),
                    or(var('B'), var('B'))
                ),
                0,
                Some(
                    and(
                        var('A'),
                        or(var('B'), var('B'))
                    ),
                )
            ),
            (
                and(
                    or(var('A'), var('A')),
                    or(var('B'), var('B'))
                ),
                1,
                Some(
                    and(
                        or(var('A'), var('A')),
                        var('B'),
                    ),
                )
            ),
        ];

        for tcase in tcases {
            let mut got = tcase.0.clone();
            let res = got.reduce(Theorem::Idempotent, tcase.1);

            if let Some(expect) = tcase.2 {
                assert!(res.is_ok() && got == expect,
                    "({} => {:?}) == {:?} {}",
                    tcase.0,
                    got,
                    expect,
                    if res.is_ok() { "ok" } else { "not ok" });

            } else {
                assert!(
                    res.is_err() && got == tcase.0,
                    "did not apply idempotent thm")

            }
        }
    }

    #[test]
    fn test_reduction_involve() {
        let tcases = vec![
            (
                not(not(one)),
                0,
                Some(one),
            ),
            (
                not(not(not(one))),
                1,
                Some(not(one)),
            ),
            (
                not(not(var('A'))),
                0,
                Some(var('A')),
            ),
        ];

        for tcase in tcases {
            let mut got = tcase.0.clone();
            let res = got.reduce(Theorem::Involve, tcase.1);

            if let Some(expect) = tcase.2 {
                assert!(res.is_ok() && got == expect,
                    "({} => {:?}) == {:?} {}",
                    tcase.0,
                    got,
                    expect,
                    if res.is_ok() { "ok" } else { "not ok" });

            } else {
                assert!(
                    res.is_err() && got == tcase.0,
                    "did not apply involve thm")

            }
        }
    }

    #[test]
    fn test_reduction_complement() {
        let tcases = vec![
            (
                or(not(one), one),
                0,
                Some(one),
            ),
            (
                or(zero, one),
                0,
                Some(one),
            ),
            (
                or(not(var('A')), var('A')),
                0,
                Some(one),
            ),
            (
                and(not(one), one),
                0,
                Some(zero),
            ),
            (
                and(zero, one),
                0,
                Some(zero),
            ),
            (
                and(not(var('A')), var('A')),
                0,
                Some(zero),
            ),
            (
                and(
                    or(
                        not(var('A')),
                        var('A'),
                    ),
                    or(
                        not(var('B')),
                        var('B'),
                    ),
                ),
                1,
                Some(
                    and(
                        or(
                            not(var('A')),
                            var('A'),
                        ),
                        one,
                    ),
                )
            ),
        ];

        for tcase in tcases {
            let mut got = tcase.0.clone();
            let res = got.reduce(Theorem::Complement, tcase.1);

            if let Some(expect) = tcase.2 {
                assert!(res.is_ok() && got == expect,
                    "({} => {:?}) == {:?} {}",
                    tcase.0,
                    got,
                    expect,
                    if res.is_ok() { "ok" } else { "not ok" });

            } else {
                assert!(
                    res.is_err() && got == tcase.0,
                    "did not apply complement thm")

            }
        }
    }

    #[test]
    fn test_reduction_commute() {
        let tcases = vec![
            (
                or(zero, one),
                0,
                Some(or(one, zero)),
            ),
            (
                or(var('A'), var('B')),
                0,
                Some(or(var('B'), var('A'))),
            ),
            (
                and(zero, one),
                0,
                Some(and(one, zero)),
            ),
            (
                and(var('A'), var('B')),
                0,
                Some(and(var('B'), var('A'))),
            ),
            (
                or(
                    one,
                    and(var('C'), var('D')),
                ),
                1,
                Some(
                    or(
                        one,
                        and(var('D'), var('C')),
                    ),
                )
            ),
            (
                or(
                    and(var('A'), var('B')),
                    and(var('C'), var('D')),
                ),
                1,
                Some(
                    or(
                        and(var('B'), var('A')),
                        and(var('C'), var('D')),
                    ),
                )
            ),
        ];

        for tcase in tcases {
            let mut got = tcase.0.clone();
            let res = got.reduce(Theorem::Commute, tcase.1);

            if let Some(expect) = tcase.2 {
                assert!(res.is_ok() && got == expect,
                    "({} => {}) == {} {}",
                    tcase.0,
                    got,
                    expect,
                    if res.is_ok() { "ok" } else { "not ok" });

            } else {
                assert!(
                    res.is_err() && got == tcase.0,
                    "did not apply commute thm")
            }
        }
    }

    #[test]
    fn test_reduction_associate() {
        let tcases = vec![
            (
                or(
                    var('A'),
                    or(
                        var('B'),
                        var('C'),
                    ),
                ),
                0,
                Some(
                    or(
                        or(
                            var('A'),
                            var('B'),
                        ),
                        var('C'),
                    ),
                ),
            ),
            (
                or(
                    var('A'),
                    or(
                        var('B'),
                        or(
                            var('C'),
                            var('D'),
                        ),
                    ),
                ),
                1,
                Some(
                    or(
                        var('A'),
                        or(
                            or(
                                var('B'),
                                var('C'),
                            ),
                            var('D'),
                        ),
                    ),
                ),
            ),
            (
                or(
                    var('A'),
                    or(
                        or(
                            var('B'),
                            var('C'),
                        ),
                        var('D'),
                    ),
                ),
                1,
                Some(
                    or(
                        var('A'),
                        or(
                            var('B'),
                            or(
                                var('C'),
                                var('D'),
                            ),
                        ),
                    ),
                ),
            ),
            (
                and(
                    and(
                        var('A'),
                        var('B'),
                    ),
                    var('C'),
                ),
                0,
                Some(
                    and(
                        var('A'),
                        and(
                            var('B'),
                            var('C'),
                        ),
                    ),
                ),
            ),
        ];

        for tcase in tcases {
            let mut got = tcase.0.clone();
            let res = got.reduce(Theorem::Associate, tcase.1);

            if let Some(expect) = tcase.2 {
                assert!(res.is_ok() && got == expect,
                    "({} => {:?}) == {:?} {}",
                    tcase.0,
                    got,
                    expect,
                    if res.is_ok() { "ok" } else { "not ok" });

            } else {
                assert!(
                    res.is_err() && got == tcase.0,
                    "did not apply associate thm")

            }
        }
    }

    #[test]
    fn test_reduction_distribute() {
        let tcases = vec![
            (
                or(
                    and(var('A'), var('B')),
                    and(var('A'), var('C')),
                ),
                0,
                Some(
                    and(
                        var('A'),
                        or(
                            var('B'),
                            var('C'),
                        )
                    )
                )
            ),
            (
                or(
                    and(var('A'), var('B')),
                    and(var('C'), var('A')),
                ),
                0,
                Some(
                    and(
                        var('A'),
                        or(
                            var('B'),
                            var('C'),
                        )
                    )
                )
            ),
            (
                or(
                    and(var('B'), var('A')),
                    and(var('A'), var('C')),
                ),
                0,
                Some(
                    and(
                        var('A'),
                        or(
                            var('B'),
                            var('C'),
                        )
                    )
                )
            ),
            (
                or(
                    and(var('B'), var('A')),
                    and(var('C'), var('A')),
                ),
                0,
                Some(
                    and(
                        var('A'),
                        or(
                            var('B'),
                            var('C'),
                        )
                    )
                )
            ),
            (
                and(
                    or(var('B'), var('A')),
                    or(var('C'), var('A')),
                ),
                0,
                Some(
                    or(
                        var('A'),
                        and(
                            var('B'),
                            var('C'),
                        )
                    )
                )
            ),
        ];

        for tcase in tcases {
            let mut got = tcase.0.clone();
            let res = got.reduce(Theorem::Distribute, tcase.1);

            if let Some(expect) = tcase.2 {
                assert!(res.is_ok() && got == expect,
                    "({} => {:?}) == {:?} {}",
                    tcase.0,
                    got,
                    expect,
                    if res.is_ok() { "ok" } else { "not ok" });

            } else {
                assert!(
                    res.is_err() && got == tcase.0,
                    "did not apply distribute thm")

            }
        }
    }
}
