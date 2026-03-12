use std::fmt::{self, Display};
use std::str::FromStr;
use std::{any::Any, sync::Arc};

use crate::*;


#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Var(String),
    Function(String, Vec<Term>),
}

impl Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(v) => write!(f, "{}", v),
            Term::Function(func, args) => {
                if args.is_empty() {
                    write!(f, "{}", func)
                } else {
                    write!(f, "({}", func)?;
                    for arg in args {
                        write!(f, " {}", arg)?;
                    }
                    write!(f, ")")
                }
            }
        }
    }
}

pub fn parse_term_rest(s: &str) -> (Term, &str) {
    let s = s.trim();
    if s.starts_with('(') {
        let mut rest = &s[1..];
        rest = rest.trim_start();
        let mut func_name = String::new();
        for c in rest.chars() {
            if c.is_whitespace() || c == ')' {
                break;
            }
            func_name.push(c);
            rest = &rest[1..];
        }
        let mut args = vec![];
        while !rest.trim_start().starts_with(')') {
            let (arg, new_rest) = parse_term_rest(rest);
            args.push(arg);
            rest = new_rest;
        }
        rest = rest.trim_start();
        rest = &rest[1..]; // skip ')'
        (Term::Function(func_name, args), rest)
    } else {
        let mut var_name = String::new();
        let mut rest = s;
        for c in rest.chars() {
            if c.is_whitespace() || c == ')' {
                break;
            }
            var_name.push(c);
            rest = &rest[1..];
        }
        if var_name.starts_with('?') {
            (Term::Var(var_name), rest)
        } else {
            (Term::Function(var_name, vec![]), rest)
        }
    }
}

pub fn parse_term(s: &str) -> Term {
    let (term, rest) = parse_term_rest(s);
    assert!(rest.trim().is_empty(), "Unexpected input after term: \"{}\" for string \"{}\"", rest, s);
    term
}

pub fn term_size(t: &Term) -> usize {
    match t {
        Term::Var(_) => 1,
        Term::Function(_, ts) => 1 + ts.iter().map(|t| term_size(t)).sum::<usize>(),
    }
}


// Critical Pair computation
// Given two rules, L1 -> R1 and L2 -> R2, find 
// all ways they overlap (i.e., L1 matches a subterm of L2 or vice versa)
// and produce the critical pairs L = unified this match, apply R1 and R2 respectively at the match site

type Rule = (Term, Term);
type VarSym = String;
pub type Substitution = (VarSym, Term);
pub type SubstitutionSet = Vec<Substitution>;

/// Returns the union of two vectors (without duplicates).
pub fn union<T: Clone + PartialEq>(mut v1: Vec<T>, v2: Vec<T>) -> Vec<T> {
    for item in v2 {
        if !v1.contains(&item) {
            v1.push(item);
        }
    }
    v1
}

/// Returns the intersection of two vectors.
pub fn intersection<T: Clone + PartialEq>(v1: Vec<T>, v2: Vec<T>) -> Vec<T> {
    v1.into_iter().filter(|x| v2.contains(x)).collect()
}

/// Subtracts all elements in `to_remove` from `v`.
pub fn subtraction<T: Clone + PartialEq>(v: Vec<T>, to_remove: Vec<T>) -> Vec<T> {
    v.into_iter().filter(|item| !to_remove.contains(item)).collect()
}

/// [vars t] returns the list of variable symbols occurring in [t].
pub fn vars(t: &Term) -> Vec<VarSym> {
    match t {
        Term::Var(v) => vec![v.clone()],
        Term::Function(_, ts) => varslist(ts),
    }
}

/// [varslist ts] returns the union (without duplicates) of the variable lists of terms.
pub fn varslist(ts: &[Term]) -> Vec<VarSym> {
    ts.iter()
        .map(|t| vars(t))
        .fold(Vec::new(), |acc, v| union(acc, v))
}


/// [rename (old, new) t] replaces all occurrences of the variable [old] with [new] in [t].
pub fn rename(r: &(VarSym, VarSym), t: &Term) -> Term {
    match t {
        Term::Var(x) if x == &r.0 => Term::Var(r.1.clone()),
        Term::Var(_) => t.clone(),
        Term::Function(f, ts) => Term::Function(f.clone(), renamelist(r, ts)),
    }
}

/// Applies [rename] to each term in the list.
pub fn renamelist(r: &(VarSym, VarSym), ts: &[Term]) -> Vec<Term> {
    ts.iter().map(|t| rename(r, t)).collect()
}

/// [uniquevarstep xis x_i n ru] looks for a fresh variant for [x_i] (of the form (x, n))
/// that is not yet in [xis] and renames [ru] accordingly. It returns the new rule and an updated list.
pub fn uniquevarstep(
    xis: &Vec<VarSym>,
    x_i: &VarSym,
    n: i32,
    ru: &Rule,
) -> (Rule, Vec<VarSym>, (VarSym,VarSym)) {
    // let candidate = VarSym(x_i.0.clone(), n);
    // let candidate = VarSym(x_i.0.clone(), n);
    let candidate = format!("{}_{}", x_i, n);
    if xis.contains(&candidate) {
        uniquevarstep(xis, x_i, n + 1, ru)
    } else {
        let (l, r) = ru;
        let new_l = rename(&(x_i.clone(), candidate.clone()), l);
        let new_r = rename(&(x_i.clone(), candidate.clone()), r);
        let new_rule = (new_l, new_r);
        let mut new_xis = xis.clone();
        new_xis.push(candidate.clone());
        new_xis = subtraction(new_xis, vec![x_i.clone()]);
        (new_rule, new_xis, (x_i.clone(), candidate))
    }
}

pub fn uniquevarsub_ref(mut xis: Vec<VarSym>, ins: Vec<VarSym>, ru: (&Term, &Term)) -> (Rule,Vec<(VarSym,VarSym)>) {
    // let mut rule_current = ru;
    let mut rule_current = (ru.0.clone(), ru.1.clone());
    let mut subst = vec![];
    for xi in ins {
        // let (new_rule, new_xis) = uniquevarstep_ref(&xis, &xi, 0, rule_current);
        let (new_rule, new_xis, new_subst) = uniquevarstep(&xis, &xi, 0, &rule_current);
        rule_current = (new_rule.0, new_rule.1);
        xis = new_xis;
        subst.push(new_subst);
    }
    (rule_current, subst)
}

pub fn uniquevar_ref(ru: (&Term, &Term), ru_prime: (&Term, &Term)) -> (Rule, Rule, Vec<(VarSym,VarSym)>) {
    let (l, r) = ru;
    let (l_prime, r_prime) = ru_prime;
    let uni = union(vars(l), vars(r)); // vars rule 1
    let ins = intersection(uni.clone(),  // get variables in both
         union(vars(l_prime), vars(r_prime)) // vars rule 2
    );
    let (new_ru_prime, subst) = uniquevarsub_ref(uni, ins, ru_prime.clone()); // rename right
    let new_ru = (l.clone(), r.clone()); // left stays
    (new_ru, new_ru_prime, subst)
}




/// Removes symmetric duplicates from a vector of pairs.
fn remove_symmetric_duplicates(pairs: Vec<(Term, Term, SubstitutionSet)>) -> Vec<(Term, Term, SubstitutionSet)> {
    let mut result = Vec::new();
    for pair in pairs.into_iter() {
        let (ref x, ref y, _) = pair;
        if x == y {
            // skip identical pairs
            continue;
        }
        if !result
            .iter()
            .any(|(a, b, _)| (a == y && b == x) || (a == x && b == y))
        {
            result.push(pair);
        }
    }
    result
}


/// Attempts to unify terms `t` and `t_prime` under the current substitution `subst`.
/// Returns `Some(new_subst)` if successful, or `None` if unification fails.
fn unify_with_subst(
    subst_var: &SubstitutionSet,
    t: &Term,
    t_prime: &Term,
) -> Option<SubstitutionSet> {
    match t {
        Term::Var(var) => {
            match t_prime {
                Term::Var(var_prime) if var == var_prime => Some(subst_var.clone()),
                _ if vars(t_prime).contains(var) => None, // Occurs check
                _ => {
                    // Extend the substitution with (var -> t_prime) and update all mappings.
                    let mut new_subst = vec![(var.clone(), t_prime.clone())];
                    new_subst.extend(subst_var.iter().map(|(x, a)| {
                        (x.clone(), subst(&vec![(var.clone(), t_prime.clone())], a))
                    }));
                    Some(new_subst)
                }
            }
        }
        Term::Function(f, ts) => match t_prime {
            Term::Var(var_prime) => {
                if vars(t).contains(var_prime) {
                    None
                } else {
                    let mut new_subst = vec![(var_prime.clone(), t.clone())];
                    new_subst.extend(subst_var.iter().map(|(x, a)| {
                        (x.clone(), subst(&vec![(var_prime.clone(), t.clone())], a))
                    }));
                    Some(new_subst)
                }
            }
            Term::Function(f_prime, ts_prime) if f == f_prime => {
                unify_term_lists(subst_var.clone(), ts, ts_prime)
            }
            _ => None,
        },
    }
}


/// Finds a substitution for a variable in a substitution set.
/// only lifetime in code
pub fn find_substitution<'a>(xi: &'a VarSym, ss: &'a SubstitutionSet) -> Option<&'a Term> {
    for (var, term) in ss {
        if var == xi {
            return Some(term);
        }
    }
    None
}


/// [subst ss t] recursively applies the substitution set [ss] to term [t].
pub fn subst(ss: &SubstitutionSet, t: &Term) -> Term {
    match t {
        Term::Var(xi) => {
            if let Some(s) = find_substitution(xi, ss) {
                s.clone()
            } else {
                t.clone()
            }
        }
        Term::Function(f, ts) => {
            let new_ts = ts.iter().map(|t| subst(ss, t)).collect();
            Term::Function(f.clone(), new_ts)
        }
    }
}

/// Unifies two lists of terms under the current substitution.
fn unify_term_lists(
    subst_var: SubstitutionSet,
    terms1: &[Term],
    terms2: &[Term],
) -> Option<SubstitutionSet> {
    if terms1.len() != terms2.len() {
        return None;
    }
    if terms1.is_empty() {
        return Some(subst_var);
    }
    let new_subst = unify_with_subst(&subst_var, &terms1[0], &terms2[0])?;
    let new_terms1: Vec<Term> = terms1[1..].iter().map(|t| subst(&new_subst, t)).collect();
    let new_terms2: Vec<Term> = terms2[1..].iter().map(|t| subst(&new_subst, t)).collect();
    unify_term_lists(new_subst, &new_terms1, &new_terms2)
}

/// A convenience function to unify two terms starting with an empty substitution.
/// (The resulting substitution is “reversed”)
fn unify(t: &Term, t_prime: &Term) -> Option<SubstitutionSet> {
    let mut s = unify_with_subst(&vec![], t, t_prime)?;
    s.reverse();
    Some(s)
}


/// Computes parts of a critical pair from `term` and a rewrite rule `(l -> r)`.
/// Returns a vector of pairs `(t, subst)` representing a potential overlap.
fn critical_pair_parts(term: &Term, rule: &Rule) -> Vec<(Term, SubstitutionSet)> {
    match term {
        Term::Var(_) => vec![],
        Term::Function(f, ts) => {
            let (l, r) = rule;
            let mut result = Vec::new();
            if let Some(s) = unify(term, l) {
                result.push((r.clone(), s));
            }
            let parts_list = critical_pair_parts_list(ts, rule);
            for (ts_prime, s) in parts_list {
                result.push((Term::Function(f.clone(), ts_prime), s));
            }
            result
        }
    }
}

/// Computes critical pair parts for a list of subterms given a rewrite rule.
fn critical_pair_parts_list(ts: &[Term], rule: &Rule) -> Vec<(Vec<Term>, SubstitutionSet)> {
    if ts.is_empty() {
        vec![]
    } else {
        let mut results = Vec::new();
        let first = &ts[0];
        let rest = &ts[1..];
        for (t_prime, s) in critical_pair_parts(first, rule) {
            let mut new_ts = vec![t_prime];
            new_ts.extend_from_slice(rest);
            results.push((new_ts, s));
        }
        for (mut ts_prime, s) in critical_pair_parts_list(rest, rule) {
            let mut new_ts = vec![first.clone()];
            new_ts.append(&mut ts_prime);
            results.push((new_ts, s));
        }
        results
    }
}

/// Applies the substitution contained in each pair to both a term and the rule’s right–hand side.
fn apply_cp_subst(r: &Term, pairs: Vec<(Term, SubstitutionSet)>) -> Vec<(Term, Term, SubstitutionSet)> {
    pairs
        .into_iter()
        .map(|(t, s)| (subst(&s, &t), subst(&s, r), s))
        .collect()
}

pub fn all_critical_pair_ref(rule1: (&Term, &Term), rule2: (&Term,&Term)) -> Vec<(Term, Term, SubstitutionSet, Vec<(VarSym,VarSym)>)> {
    // Assume that `uniquevar` takes a pair of rules and returns a pair with variables renamed apart.
    let (rule1_prime, rule2_prime, prime_subst) = uniquevar_ref(rule1, rule2);
    let (l1, r1) = &rule1_prime;
    let (l2, r2) = &rule2_prime;
    let mut pairs = Vec::new();
    pairs.extend(apply_cp_subst(r1, critical_pair_parts(l1, &rule2_prime)));
    pairs.extend(apply_cp_subst(r2, critical_pair_parts(l2, &rule1_prime)));
    remove_symmetric_duplicates(pairs)
    .into_iter().map(|(x,y, unifier)| (x,y,unifier,prime_subst.clone())).collect()
}



pub fn equation_to_rewrite<L: Language + Send + Sync + 'static, N: Analysis<L> + 'static>(x: Pattern<L>, y: Pattern<L>, name: String) -> Rewrite<L, N> {
    let x_str = x.to_string();
    let y_str = y.to_string();
    // Rewrite::new(name, x_str, y_str, vec![], None::<Arc<dyn Condition<L, N>>>, x, y).unwrap()
    Rewrite::new(name, x_str, y_str, x, y).unwrap()
}

pub fn rule_of_cp<L: Language + Send + Sync + 'static, N: Analysis<L> + 'static>(rule_name: &str, lhs: &Term, rhs: &Term) -> Rewrite<L, N> {
    let lhs_pattern = Pattern::from_str(&lhs.to_string()).unwrap();
    let rhs_pattern = Pattern::from_str(&rhs.to_string()).unwrap();
    equation_to_rewrite(lhs_pattern, rhs_pattern, format!("cp-{}", rule_name))
}



// pub fn equation_to_rewrite_cond<L: Language + Send + Sync + 'static, N: Analysis<L>>(x: Pattern<L>, y: Pattern<L>, name: String, conds_str: Vec<String>, conds: Option<impl Fn(&mut EGraph<L, N>, Id, &Subst) -> bool>) -> Rewrite<L, N> {
// pub fn equation_to_rewrite_cond<L, N, F>(
//     x: Pattern<L>,
//     y: Pattern<L>,
//     name: String,
//     conds_str: Vec<String>,
//     conds: Option<F>,
//     // conds: Option<Box<dyn Condition<L,N>>>
// ) -> Rewrite<L, N>
// where
//     L: Language + Send + Sync + 'static,
//     N: Analysis<L> + 'static,
//     F: Condition<L,N> + 'static,
// {
//     let x_str = x.to_string();
//     let y_str = y.to_string();
//     // Convert the provided condition into an Arc<dyn Condition<..>> so we can both
//     // use it to build the ConditionalApplier and pass it into Rewrite::new.
//     let conds_arc: Option<Arc<dyn Condition<L, N>>> =
//         conds.map(|c| Arc::new(c) as Arc<dyn Condition<L, N>>);

//     let applier = if let Some(cond_arc) = conds_arc.clone() {
//         let cond_applier = ConditionalApplier {
//             condition: cond_arc,
//             applier: y,
//             // _marker: std::marker::PhantomData,
//         };
//         CombinedApplier::WithCondition(cond_applier)
//     } else {
//         CombinedApplier::Plain(Arc::new(y))
//     };

//     Rewrite::new(name, x_str, y_str, conds_str, conds_arc, x, applier).unwrap()
// }

// ["crate::trs::is_const_pos(\"?z\")", "crate::trs::is_const_pos(\"?c\")"]
// pub fn rule_of_cp_cond<L: Language + Send + Sync + 'static, N: Analysis<L>>(rule_name: &str, lhs: &Term, rhs: &Term, conds_str: Vec<String>, conds: Option<impl Fn(&mut EGraph<L, N>, Id, &Subst) -> bool>) -> Rewrite<L, N> {
// pub fn rule_of_cp_cond<L, N, F>(rule_name: &str, lhs: &Term, rhs: &Term, conds_str: Vec<String>, 
//     conds: Option<F>
//     // conds: Option<Box<dyn Condition<L,N>>>
// ) -> Rewrite<L, N>
// where
//     L: Language + Send + Sync + 'static,
//     N: Analysis<L> + 'static,
//     F: Condition<L,N> + 'static
// {
//     let lhs_pattern = Pattern::from_str(&lhs.to_string()).unwrap();
//     let rhs_pattern = Pattern::from_str(&rhs.to_string()).unwrap();
//     equation_to_rewrite_cond(lhs_pattern, rhs_pattern, format!("cp-{}", rule_name), conds_str, conds)
// }


// #[derive(Clone, Debug)]
// pub struct PotentialConditionalApplier<C, A> {
//     pub condition: Option<C>,
//     pub applier: A,
// }

pub enum CombinedApplier<C, A, N, L> {
    WithCondition(ConditionalApplier<C, A>), // Your custom struct
    // Plain(Pattern<L>),                       // The basic pattern
    Plain(Arc<dyn Applier<L, N>>)
}

impl<C, A, N, L> Applier<L, N> for CombinedApplier<C, A, N, L>
where
    L: Language,
    C: Condition<L, N>,
    A: Applier<L, N>,
    N: Analysis<L>,
{
    fn apply_one(&self, egraph: &mut EGraph<L, N>, eclass: Id, subst: &Subst) -> Vec<Id> {
        match self {
            // DELEGATION HAPPENS HERE:
            // We just call .apply_one() on the inner object.
            CombinedApplier::WithCondition(c) => c.apply_one(egraph, eclass, subst),
            CombinedApplier::Plain(p) => p.apply_one(egraph, eclass, subst),
        }
    }
    
    fn vars(&self) -> Vec<Var> {
        match self {
            CombinedApplier::WithCondition(c) => c.vars(),
            CombinedApplier::Plain(p) => p.vars(),
        }
    }
}


























/// A rewrite that searches for the lefthand side and applies the righthand side.
///
/// The [`rewrite!`] is the easiest way to create rewrites.
///
/// A [`Rewrite`] consists principally of a [`Searcher`] (the lefthand
/// side) and an [`Applier`] (the righthand side).
/// It additionally stores a name used to refer to the rewrite and a
/// long name used for debugging.
///
#[derive(Clone)]
#[non_exhaustive]
pub struct Rewrite<L, N> {
    /// The name of the rewrite.
    pub name: String,
    // lhs: String,
    // rhs: String,
    pub lhs: Term,
    pub rhs: Term,
    // pub cond: Vec<String>,
    // pub conds: Option<Arc<dyn Condition<L,N>>>,
    /// The searcher (left-hand side) of the rewrite.
    pub searcher: Arc<dyn Searcher<L, N>>,
    /// The applier (right-hand side) of the rewrite.
    pub applier: Arc<dyn Applier<L, N>>,
}

impl<L, N> fmt::Debug for Rewrite<L, N>
where
    L: Language + 'static,
    N: 'static,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Rewrite");
        d.field("name", &self.name);

        if let Some(pat) = Any::downcast_ref::<Pattern<L>>(&self.searcher) {
        // if let Some(pat) = (&*self.searcher as &dyn Any).downcast_ref::<Pattern<L>>() {
            d.field("searcher", &DisplayAsDebug(pat));
        } else {
            d.field("searcher", &"<< searcher >>");
        }

        if let Some(pat) = Any::downcast_ref::<Pattern<L>>(&self.applier) {
        // if let Some(pat) = (&*self.applier as &dyn Any).downcast_ref::<Pattern<L>>() {
            d.field("applier", &DisplayAsDebug(pat));
        } else {
            d.field("applier", &"<< applier >>");
        }

        d.finish()
    }
}

impl<L, N> Rewrite<L, N> {
    /// Returns the name of the rewrite.
    pub fn name(&self) -> &str {
        &self.name
    }
}

impl<L: Language, N: Analysis<L>> Rewrite<L, N> {
    /// Create a new [`Rewrite`]. You typically want to use the
    /// [`rewrite!`] macro instead.
    ///
    pub fn new(
        name: impl Into<String>,
        lhs: String,
        rhs: String,
        // cond: Vec<String>,
        // conds: Option<impl Condition<L,N> + 'static>,
        // conds: Option<Arc<dyn Condition<L,N>>>,
        searcher: impl Searcher<L, N> + 'static,
        applier: impl Applier<L, N> + 'static,
    ) -> Result<Self, String> {
        let name = name.into();
        let searcher = Arc::new(searcher);
        let applier = Arc::new(applier);
        // println!("Creating rewrite {} with conditions: {:?}", name, cond);
        // let conds = conds.map(|c| Arc::new(c) as Arc<dyn Condition<L,N>>);

        let bound_vars = searcher.vars();
        for v in applier.vars() {
            if !bound_vars.contains(&v) {
                return Err(format!("Rewrite {} refers to unbound var {}", name, v));
            }
        }

        Ok(Self {
            name,
            lhs: parse_term(&lhs),
            rhs: parse_term(&rhs),
            // cond,
            // conds,
            searcher,
            applier,
        })
    }

    /// Call [`search`] on the [`Searcher`].
    ///
    /// [`search`]: Searcher::search()
    pub fn search(&self, egraph: &EGraph<L, N>) -> Vec<SearchMatches> {
        self.searcher.search(egraph)
    }

    /// Call [`apply_matches`] on the [`Applier`].
    ///
    /// [`apply_matches`]: Applier::apply_matches()
    pub fn apply(&self, egraph: &mut EGraph<L, N>, matches: &[SearchMatches]) -> Vec<Id> {
        self.applier.apply_matches(egraph, matches)
    }

    /// This `run` is for testing use only. You should use things
    /// from the `egg::run` module
    #[cfg(test)]
    pub(crate) fn run(&self, egraph: &mut EGraph<L, N>) -> Vec<Id> {
        let start = crate::util::Instant::now();

        let matches = self.search(egraph);
        log::debug!("Found rewrite {} {} times", self.name, matches.len());

        let ids = self.apply(egraph, &matches);
        let elapsed = start.elapsed();
        log::debug!(
            "Applied rewrite {} {} times in {}.{:03}",
            self.name,
            ids.len(),
            elapsed.as_secs(),
            elapsed.subsec_millis()
        );

        egraph.rebuild();
        ids
    }
}

/// Helper to construct a `Rewrite` when the condition is given as a closure.
/// This wraps the closure in `FnCondition` and boxes it into an `Arc<dyn Condition<..>>`.
// pub fn new_with_condition<L, N, F, S, A>(
//     name: impl Into<String>,
//     lhs: String,
//     rhs: String,
//     cond: Vec<String>,
//     conds: F,
//     searcher: S,
//     applier: A,
// ) -> Rewrite<L, N>
// where
//     L: Language + Send + Sync + 'static,
//     N: Analysis<L> + 'static,
//     F: Fn(&mut EGraph<L, N>, Id, &Subst) -> bool + 'static,
//     S: Searcher<L, N> + 'static,
//     A: Applier<L, N> + 'static,
// {
//     let conds_arc: Option<Arc<dyn Condition<L, N>>> =
//         Some(Arc::new(FnCondition(conds)) as Arc<dyn Condition<L, N>>);
//     Rewrite::new(name, lhs, rhs, cond, conds_arc, searcher, applier).unwrap()
// }
pub fn new_with_condition<L, N, S, A>(
    name: impl Into<String>,
    lhs: String,
    rhs: String,
    // cond: Vec<String>,
    // conds: F,
    searcher: S,
    applier: A,
) -> Rewrite<L, N>
where
    L: Language + Send + Sync + 'static,
    N: Analysis<L> + 'static,
    // F: Fn(&mut EGraph<L, N>, Id, &Subst) -> bool + 'static,
    S: Searcher<L, N> + 'static,
    A: Applier<L, N> + 'static,
{
    // let conds_arc: Option<Arc<dyn Condition<L, N>>> =
    //     Some(Arc::new(FnCondition(conds)) as Arc<dyn Condition<L, N>>);
    // Rewrite::new(name, lhs, rhs, cond, conds_arc, searcher, applier).unwrap()
    Rewrite::new(name, lhs, rhs, searcher, applier).unwrap()
}


/// The lefthand side of a [`Rewrite`].
///
/// A [`Searcher`] is something that can search the egraph and find
/// matching substititions.
/// Right now the only significant [`Searcher`] is [`Pattern`].
///
pub trait Searcher<L, N>
where
    L: Language,
    N: Analysis<L>,
{
    /// Search one eclass, returning None if no matches can be found.
    /// This should not return a SearchMatches with no substs.
    fn search_eclass(&self, egraph: &EGraph<L, N>, eclass: Id) -> Option<SearchMatches>;

    /// Search the whole [`EGraph`], returning a list of all the
    /// [`SearchMatches`] where something was found.
    /// This just calls [`search_eclass`] on each eclass.
    ///
    /// [`search_eclass`]: Searcher::search_eclass
    fn search(&self, egraph: &EGraph<L, N>) -> Vec<SearchMatches> {
        egraph
            .classes()
            .filter_map(|e| self.search_eclass(egraph, e.id))
            .collect()
    }

    /// Returns a list of the variables bound by this Searcher
    fn vars(&self) -> Vec<Var>;
}

/// The righthand side of a [`Rewrite`].
///
/// An [`Applier`] is anything that can do something with a
/// substitition ([`Subst`]). This allows you to implement rewrites
/// that determine when and how to respond to a match using custom
/// logic, including access to the [`Analysis`] data of an [`EClass`].
///
/// Notably, [`Pattern`] implements [`Applier`], which suffices in
/// most cases.
/// Additionally, `egg` provides [`ConditionalApplier`] to stack
/// [`Condition`]s onto an [`Applier`], which in many cases can save
/// you from having to implement your own applier.
///
/// # Example
/// ```
/// use egg::{rewrite as rw, *};
///
/// define_language! {
///     enum Math {
///         Num(i32),
///         "+" = Add([Id; 2]),
///         "*" = Mul([Id; 2]),
///         Symbol(Symbol),
///     }
/// }
///
/// type EGraph = egg::EGraph<Math, MinSize>;
///
/// // Our metadata in this case will be size of the smallest
/// // represented expression in the eclass.
/// #[derive(Default)]
/// struct MinSize;
/// impl Analysis<Math> for MinSize {
///     type Data = usize;
///     fn merge(&self, to: &mut Self::Data, from: Self::Data) -> Option<std::cmp::Ordering> {
///         Some(merge_min(to, from))
///     }
///     fn make(egraph: &EGraph, enode: &Math) -> Self::Data {
///         let get_size = |i: Id| egraph[i].data;
///         AstSize.cost(enode, get_size)
///     }
/// }
///
/// let rules = &[
///     rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
///     rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
///     rw!("add-0"; "(+ ?a 0)" => "?a"),
///     rw!("mul-0"; "(* ?a 0)" => "0"),
///     rw!("mul-1"; "(* ?a 1)" => "?a"),
///     // the rewrite macro parses the rhs as a single token tree, so
///     // we wrap it in braces (parens work too).
///     rw!("funky"; "(+ ?a (* ?b ?c))" => { Funky {
///         a: "?a".parse().unwrap(),
///         b: "?b".parse().unwrap(),
///         c: "?c".parse().unwrap(),
///     }}),
/// ];
///
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct Funky {
///     a: Var,
///     b: Var,
///     c: Var,
/// }
///
/// impl Applier<Math, MinSize> for Funky {
///     fn apply_one(&self, egraph: &mut EGraph, matched_id: Id, subst: &Subst) -> Vec<Id> {
///         let a: Id = subst[self.a];
///         // In a custom Applier, you can inspect the analysis data,
///         // which is powerful combination!
///         let size_of_a = egraph[a].data;
///         if size_of_a > 50 {
///             println!("Too big! Not doing anything");
///             vec![]
///         } else {
///             // we're going to manually add:
///             // (+ (+ ?a 0) (* (+ ?b 0) (+ ?c 0)))
///             // to be unified with the original:
///             // (+    ?a    (*    ?b       ?c   ))
///             let b: Id = subst[self.b];
///             let c: Id = subst[self.c];
///             let zero = egraph.add(Math::Num(0));
///             let a0 = egraph.add(Math::Add([a, zero]));
///             let b0 = egraph.add(Math::Add([b, zero]));
///             let c0 = egraph.add(Math::Add([c, zero]));
///             let b0c0 = egraph.add(Math::Mul([b0, c0]));
///             let a0b0c0 = egraph.add(Math::Add([a0, b0c0]));
///             // NOTE: we just return the id according to what we
///             // want unified with matched_id. The `apply_matches`
///             // method actually does the union, _not_ `apply_one`.
///             vec![a0b0c0]
///         }
///     }
/// }
///
/// let start = "(+ x (* y z))".parse().unwrap();
/// Runner::default().with_expr(&start).run(rules);
/// ```
pub trait Applier<L, N>
where
    L: Language,
    N: Analysis<L>,
{
    /// Apply many substititions.
    ///
    /// This method should call [`apply_one`] for each match and then
    /// unify the results with the matched eclass.
    /// This should return a list of [`Id`]s where the union actually
    /// did something.
    ///
    /// The default implementation does this and should suffice for
    /// most use cases.
    ///
    /// [`apply_one`]: Applier::apply_one()
    fn apply_matches(&self, egraph: &mut EGraph<L, N>, matches: &[SearchMatches]) -> Vec<Id> {
        let mut added = vec![];
        for mat in matches {
            for subst in &mat.substs {
                let ids = self
                    .apply_one(egraph, mat.eclass, subst)
                    .into_iter()
                    .filter_map(|id| {
                        let (to, did_something) = egraph.union(id, mat.eclass);
                        if did_something {
                            Some(to)
                        } else {
                            None
                        }
                    });
                added.extend(ids)
            }
        }
        added
    }

    /// Apply a single substitition.
    ///
    /// An [`Applier`] should only add things to the egraph here,
    /// _not_ union them with the id `eclass`.
    /// That is the responsibility of the [`apply_matches`] method.
    /// The `eclass` parameter allows the implementer to inspect the
    /// eclass where the match was found if they need to.
    ///
    /// This should return a list of [`Id`]s of things you'd like to
    /// be unioned with `eclass`. There can be zero, one, or many.
    ///
    /// [`apply_matches`]: Applier::apply_matches()
    fn apply_one(&self, egraph: &mut EGraph<L, N>, eclass: Id, subst: &Subst) -> Vec<Id>;

    /// Returns a list of variables that this Applier assumes are bound.
    ///
    /// `egg` will check that the corresponding `Searcher` binds those
    /// variables.
    /// By default this return an empty `Vec`, which basically turns off the
    /// checking.
    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// An [`Applier`] that checks a [`Condition`] before applying.
///
/// A [`ConditionalApplier`] simply calls [`check`] on the
/// [`Condition`] before calling [`apply_one`] on the inner
/// [`Applier`].
///
/// See the [`rewrite!`] macro documentation for an example.
///
/// [`apply_one`]: Applier::apply_one()
/// [`check`]: Condition::check()
#[derive(Clone, Debug)]
pub struct ConditionalApplier<C, A> {
    /// The [`Condition`] to [`check`] before calling [`apply_one`] on
    /// `applier`.
    ///
    /// [`apply_one`]: Applier::apply_one()
    /// [`check`]: Condition::check()
    pub condition: C,
    /// The inner [`Applier`] to call once `condition` passes.
    ///
    pub applier: A,
}

impl<C, A, N, L> Applier<L, N> for ConditionalApplier<C, A>
where
    L: Language,
    C: Condition<L, N>,
    A: Applier<L, N>,
    N: Analysis<L>,
{
    fn apply_one(&self, egraph: &mut EGraph<L, N>, eclass: Id, subst: &Subst) -> Vec<Id> {
        if self.condition.check(egraph, eclass, subst) {
            self.applier.apply_one(egraph, eclass, subst)
        } else {
            vec![]
        }
    }

    fn vars(&self) -> Vec<Var> {
        let mut vars = self.applier.vars();
        vars.extend(self.condition.vars());
        vars
    }
}

/// A condition to check in a [`ConditionalApplier`].
///
/// See the [`ConditionalApplier`] docs.
///
/// Notably, any function ([`Fn`]) that doesn't mutate other state
/// and matches the signature of [`check`] implements [`Condition`].
///
/// [`check`]: Condition::check()
/// [`Fn`]: std::ops::Fn
pub trait Condition<L, N>
where
    L: Language,
    N: Analysis<L>,
{
    /// Check a condition.
    ///
    /// `eclass` is the eclass [`Id`] where the match (`subst`) occured.
    /// If this is true, then the [`ConditionalApplier`] will fire.
    ///
    fn check(&self, egraph: &mut EGraph<L, N>, eclass: Id, subst: &Subst) -> bool;

    /// Returns a list of variables that this Condition assumes are bound.
    ///
    /// `egg` will check that the corresponding `Searcher` binds those
    /// variables.
    /// By default this return an empty `Vec`, which basically turns off the
    /// checking.
    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

impl<L, F, N> Condition<L, N> for F
where
    L: Language,
    N: Analysis<L>,
    // F: Fn(&mut EGraph<L, N>, Id, &Subst) -> bool,
    F: for<'a> Fn(&mut EGraph<L, N>, Id, &Subst) -> bool,
{
    fn check(&self, egraph: &mut EGraph<L, N>, eclass: Id, subst: &Subst) -> bool {
        self(egraph, eclass, subst)
    }
}

impl<L, N> Condition<L, N> for Arc<dyn Condition<L, N>>
where
    L: Language,
    N: Analysis<L>,
{
    fn check(&self, egraph: &mut EGraph<L, N>, eclass: Id, subst: &Subst) -> bool {
        (**self).check(egraph, eclass, subst)
    }
    fn vars(&self) -> Vec<Var> {
        (**self).vars()
    }
}

pub struct FnCondition<F>(pub F);

impl<L, N, F> Condition<L, N> for FnCondition<F>
where
    L: Language,
    N: Analysis<L>,
    F: Fn(&mut EGraph<L, N>, Id, &Subst) -> bool + 'static,
{
    fn check(&self, egraph: &mut EGraph<L, N>, eclass: Id, subst: &Subst) -> bool {
        (self.0)(egraph, eclass, subst)
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}


pub struct CombinedCondition<L,N>(pub Arc<dyn Condition<L, N>>, pub Arc<dyn Condition<L, N>>);

impl<L, N> Condition<L, N> for CombinedCondition<L, N> 
where
    L: Language,
    N: Analysis<L>,
{
    fn check(&self, egraph: &mut EGraph<L, N>, eclass: Id, subst: &Subst) -> bool {
        let first_check = self.0.check(egraph, eclass, subst);
        let second_check = self.1.check(egraph, eclass, subst);
        first_check && second_check
    }
}

/// A [`Condition`] that checks if two terms are equivalent.
///
/// This condition adds its two [`Applier`]s to the egraph and passes
/// if and only if they are equivalent (in the same eclass).
///
pub struct ConditionEqual<A1, A2>(pub A1, pub A2);

impl<L: Language> ConditionEqual<Pattern<L>, Pattern<L>> {
    /// Create a ConditionEqual by parsing two pattern strings.
    ///
    /// This panics if the parsing fails.
    pub fn parse(a1: &str, a2: &str) -> Self {
        Self(a1.parse().unwrap(), a2.parse().unwrap())
    }
}

impl<L, N, A1, A2> Condition<L, N> for ConditionEqual<A1, A2>
where
    L: Language,
    N: Analysis<L>,
    A1: Applier<L, N>,
    A2: Applier<L, N>,
{
    fn check(&self, egraph: &mut EGraph<L, N>, eclass: Id, subst: &Subst) -> bool {
        let a1 = self.0.apply_one(egraph, eclass, subst);
        let a2 = self.1.apply_one(egraph, eclass, subst);
        assert_eq!(a1.len(), 1);
        assert_eq!(a2.len(), 1);
        a1[0] == a2[0]
    }

    fn vars(&self) -> Vec<Var> {
        let mut vars = self.0.vars();
        vars.extend(self.1.vars());
        vars
    }
}

#[cfg(test)]
mod tests {

    use crate::{SymbolLang as S, *};
    use std::str::FromStr;

    type EGraph = crate::EGraph<S, ()>;

    #[test]
    fn conditional_rewrite() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let x = egraph.add(S::leaf("x"));
        let y = egraph.add(S::leaf("2"));
        let mul = egraph.add(S::new("*", vec![x, y]));

        let true_pat = Pattern::from_str("TRUE").unwrap();
        let true_id = egraph.add(S::leaf("TRUE"));

        let pow2b = Pattern::from_str("(is-power2 ?b)").unwrap();
        let mul_to_shift = rewrite!(
            "mul_to_shift";
            "(* ?a ?b)" => "(>> ?a (log2 ?b))"
            if ConditionEqual(pow2b, true_pat)
        );

        println!("rewrite shouldn't do anything yet");
        egraph.rebuild();
        let apps = mul_to_shift.run(&mut egraph);
        assert!(apps.is_empty());

        println!("Add the needed equality");
        let two_ispow2 = egraph.add(S::new("is-power2", vec![y]));
        egraph.union(two_ispow2, true_id);

        println!("Should fire now");
        egraph.rebuild();
        let apps = mul_to_shift.run(&mut egraph);
        assert_eq!(apps, vec![egraph.find(mul)]);
    }

    #[test]
    fn fn_rewrite() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let start = RecExpr::from_str("(+ x y)").unwrap();
        let goal = RecExpr::from_str("xy").unwrap();

        let root = egraph.add_expr(&start);

        fn get(egraph: &EGraph, id: Id) -> Symbol {
            egraph[id].nodes[0].op
        }

        #[derive(Debug)]
        struct Appender;
        impl Applier<SymbolLang, ()> for Appender {
            fn apply_one(&self, egraph: &mut EGraph, _eclass: Id, subst: &Subst) -> Vec<Id> {
                let a: Var = "?a".parse().unwrap();
                let b: Var = "?b".parse().unwrap();
                let a = get(&egraph, subst[a]);
                let b = get(&egraph, subst[b]);
                let s = format!("{}{}", a, b);
                vec![egraph.add(S::leaf(&s))]
            }
        }

        let fold_add = rewrite!(
            "fold_add"; "(+ ?a ?b)" => { Appender }
        );

        egraph.rebuild();
        fold_add.run(&mut egraph);
        assert_eq!(egraph.equivs(&start, &goal), vec![egraph.find(root)]);
    }
}
