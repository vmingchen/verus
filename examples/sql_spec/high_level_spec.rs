// High-Level Specification for SQL Operators in Verus
// Based on "A Coq formalisation of SQL's execution engines"

use vstd::prelude::*;

verus! {

// Core data type representing a tuple (row)
#[derive(PartialEq, Eq, Clone)]
pub struct Tuple {
    pub values: Vec<i64>, // Executable type for compatibility
}

// Atomic predicates for formulas
#[derive(PartialEq, Eq, Clone)]
pub enum AtomicFormula {
    True,
    Eq(usize, i64),          // column == value
    Lt(usize, i64),          // column < value
    Gt(usize, i64),          // column > value
    Between(usize, i64, i64), // column between low and high
}

// Multiset/Bag representation using number of occurrences
pub type Bag = Seq<Tuple>;

// Number of occurrences of an element in a bag
pub open spec fn nb_occ(t: Tuple, bag: Bag) -> nat
    decreases bag.len()
{
    if bag.len() == 0 {
        0nat
    } else {
        let count = if bag[0] == t { 1nat } else { 0nat };
        count + nb_occ(t, bag.subrange(1, bag.len() as int))
    }
}

// TODO: Fix spec_fn closure issues
// High-level specification for filter operator - commented out due to spec_fn closure issues
// A filter operation is valid if the number of occurrences of each tuple
// in the result equals the occurrences in the input multiplied by the filter condition
/*
pub open spec fn is_a_filter_op<F>(
    input: Bag,
    output: Bag,
    f: F,
) -> bool
    where F: Fn(Tuple) -> bool
{
    forall |t: Tuple|
        nb_occ(t, output) == nb_occ(t, input) * (if f(t) { 1nat } else { 0nat })
}
*/

// Group represents a collection of tuples that share the same grouping key
pub struct Group {
    pub key: Seq<int>,        // Grouping key values
    pub tuples: Seq<Tuple>,   // Tuples in this group
}

// Aggregate function type
#[derive(PartialEq, Eq, Structural)]
pub enum AggOp {
    Count,
    Sum(usize),   // Sum of column at index
    Avg(usize),   // Average of column at index
    Min(usize),
    Max(usize),
}

// Formula types (executable, Vec-based)
pub type Conjunction = Vec<AtomicFormula>;

#[derive(PartialEq, Eq, Clone)]
pub struct Formula {
    pub disjuncts: Vec<Conjunction>,
}

// Note: eval_atomic is defined in sql_algebra.rs and works with both Vec and Seq based tuples
// Import it with: use crate::sql_algebra::eval_atomic;

// Evaluate conjunction on a tuple (all atoms must be true) - Vec-based
pub open spec fn eval_conjunction(tuple: Tuple, conj: Conjunction) -> bool {
    forall|i: int| 0 <= i < conj.len() ==> crate::sql_algebra::eval_atomic(tuple, conj@[i])
}

// Evaluate DNF formula on a tuple (at least one conjunction must be true) - Vec-based
pub open spec fn eval_formula(tuple: Tuple, formula: Formula) -> bool {
    exists|i: int| 0 <= i < formula.disjuncts.len() && eval_conjunction(tuple, formula.disjuncts@[i])
}

// TODO: Fix spec_fn closure issues
// High-level specification for grouping operator - commented out due to spec_fn closure issues
/*
pub open spec fn is_a_grouping_op<G, F, B>(
    input: Bag,
    output: Bag,
    mk_groups: G,
    filter_group: F,
    build_tuple: B,
) -> bool
    where
        G: Fn(Bag) -> Seq<Group>,
        F: Fn(Group) -> bool,
        B: Fn(Group) -> Tuple,
{
    let groups = mk_groups(input);
    let filtered_groups = filter_groups(groups, filter_group);

    forall |t: Tuple|
        nb_occ(t, output) == count_in_built_groups(t, filtered_groups, build_tuple)
}

// Helper: filter groups by a predicate
pub open spec fn filter_groups<F>(groups: Seq<Group>, f: F) -> Seq<Group>
    where F: Fn(Group) -> bool
    decreases groups.len()
{
    if groups.len() == 0 {
        Seq::empty()
    } else {
        let rest = filter_groups(groups.subrange(1, groups.len() as int), f);
        if f(groups[0]) {
            seq![groups[0]].add(rest)
        } else {
            rest
        }
    }
}

// Helper: count occurrences of tuple in built groups
pub open spec fn count_in_built_groups<B>(
    t: Tuple,
    groups: Seq<Group>,
    build: B
) -> nat
    where B: Fn(Group) -> Tuple
    decreases groups.len()
{
    if groups.len() == 0 {
        0nat
    } else {
        let count = if build(groups[0]) == t { 1nat } else { 0nat };
        count + count_in_built_groups(t, groups.subrange(1, groups.len() as int), build)
    }
}
*/

// Aggregate result from a group
pub open spec fn apply_aggregate(agg: AggOp, group: Group) -> int {
    match agg {
        AggOp::Count => group.tuples.len() as int,
        AggOp::Sum(col_idx) => sum_column(group.tuples, col_idx as int),
        AggOp::Avg(col_idx) => {
            if group.tuples.len() == 0 {
                0
            } else {
                sum_column(group.tuples, col_idx as int) / group.tuples.len() as int
            }
        },
        AggOp::Min(col_idx) => min_column(group.tuples, col_idx as int),
        AggOp::Max(col_idx) => max_column(group.tuples, col_idx as int),
    }
}

// Helper: sum values in a column
pub open spec fn sum_column(tuples: Seq<Tuple>, col_idx: int) -> int
    decreases tuples.len()
{
    if tuples.len() == 0 {
        0
    } else {
        tuples[0].values@[col_idx] as int + sum_column(tuples.subrange(1, tuples.len() as int), col_idx)
    }
}

// Helper: minimum value in a column
pub open spec fn min_column(tuples: Seq<Tuple>, col_idx: int) -> int
    decreases tuples.len()
{
    if tuples.len() == 0 {
        i32::MAX as int
    } else if tuples.len() == 1 {
        tuples[0].values@[col_idx] as int
    } else {
        let rest_min = min_column(tuples.subrange(1, tuples.len() as int), col_idx);
        let current_val = tuples[0].values@[col_idx] as int;
        if current_val < rest_min {
            current_val
        } else {
            rest_min
        }
    }
}

// Helper: maximum value in a column
pub open spec fn max_column(tuples: Seq<Tuple>, col_idx: int) -> int
    decreases tuples.len()
{
    if tuples.len() == 0 {
        i32::MIN as int
    } else if tuples.len() == 1 {
        tuples[0].values@[col_idx] as int
    } else {
        let rest_max = max_column(tuples.subrange(1, tuples.len() as int), col_idx);
        let current_val = tuples[0].values@[col_idx] as int;
        if current_val > rest_max {
            current_val
        } else {
            rest_max
        }
    }
}

} // verus!
