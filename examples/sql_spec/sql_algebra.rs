// SQL Algebra: Logical operators with formal semantics
// Based on Section 5 of the SQL formalization paper

use vstd::prelude::*;
use crate::high_level_spec::*;

verus! {

// SQL Query abstract syntax tree
pub enum Query {
    Table(TableName),
    Filter(Box<Query>, FormulaSpec),
    GroupBy(Box<Query>, Vec<usize>, FormulaSpec, Vec<AggOp>), // grouping cols, having, aggregates
}

pub type TableName = nat;

// ============================================================================
// Formula in DNF (Disjunctive Normal Form) - No Recursion
// ============================================================================
// AtomicFormula, Formula, and Conjunction are now imported from high_level_spec.rs

// For spec purposes, we also define Seq-based versions
pub type ConjunctionSpec = Seq<AtomicFormula>;

pub struct FormulaSpec {
    pub disjuncts: Seq<ConjunctionSpec>,
}

// Evaluate atomic formula on a tuple
// Note: Compares i64 (from Tuple.values) with i64 (from AtomicFormula)
pub open spec fn eval_atomic(tuple: Tuple, atom: AtomicFormula) -> bool {
    match atom {
        AtomicFormula::True => true,
        AtomicFormula::Eq(col, val) => col < tuple.values@.len() && tuple.values@[col as int] == val,
        AtomicFormula::Lt(col, val) => col < tuple.values@.len() && tuple.values@[col as int] < val,
        AtomicFormula::Gt(col, val) => col < tuple.values@.len() && tuple.values@[col as int] > val,
        AtomicFormula::Between(col, low, high) => {
            col < tuple.values@.len() && tuple.values@[col as int] >= low && tuple.values@[col as int] <= high
        },
    }
}

// Evaluate conjunction on a tuple (all atoms must be true)
pub open spec fn eval_conjunction_spec(tuple: Tuple, conj: ConjunctionSpec) -> bool {
    forall|i: int| 0 <= i < conj.len() ==> eval_atomic(tuple, conj[i])
}

// Evaluate DNF formula on a tuple (at least one conjunction must be true)
pub open spec fn eval_formula_spec(tuple: Tuple, formula: FormulaSpec) -> bool {
    exists|i: int| 0 <= i < formula.disjuncts.len() && eval_conjunction_spec(tuple, formula.disjuncts[i])
}

// Database instance: maps table names to bags
pub type Instance = Map<TableName, Bag>;

// Evaluate a query in an instance
pub open spec fn eval_query(instance: Instance, query: Query) -> Bag
    decreases query
{
    match query {
        Query::Table(name) => {
            if instance.contains_key(name) {
                instance[name]
            } else {
                Seq::empty()
            }
        },
        Query::Filter(q, formula) => {
            let input = eval_query(instance, *q);
            filter_by_formula(input, formula)
        },
        Query::GroupBy(q, group_cols, having, aggs) => {
            let input = eval_query(instance, *q);
            eval_group_by(input, group_cols, having, aggs)
        },
    }
}

// Filter bag by formula
pub open spec fn filter_by_formula(bag: Bag, formula: FormulaSpec) -> Bag
    decreases bag.len()
{
    if bag.len() == 0 {
        Seq::empty()
    } else {
        let rest = filter_by_formula(bag.subrange(1, bag.len() as int), formula);
        if eval_formula_spec(bag[0], formula) {
            seq![bag[0]].add(rest)
        } else {
            rest
        }
    }
}

// Evaluate GROUP BY with HAVING clause
pub open spec fn eval_group_by(
    input: Bag,
    group_cols: Vec<usize>,
    having: FormulaSpec,
    aggs: Vec<AggOp>
) -> Bag {
    let groups = partition_by_cols(input, group_cols@);
    let filtered_groups = filter_groups_by_having(groups, having);
    build_result_tuples(filtered_groups, aggs@)
}

// Partition tuples into groups based on grouping columns
pub open spec fn partition_by_cols(bag: Bag, group_cols: Seq<usize>) -> Seq<Group>
    decreases bag.len()
{
    if bag.len() == 0 {
        Seq::empty()
    } else {
        let tuple = bag[0];
        let key = extract_key(tuple, group_cols);
        let rest_groups = partition_by_cols(bag.subrange(1, bag.len() as int), group_cols);
        add_to_groups(tuple, key, rest_groups)
    }
}

// Extract grouping key from tuple
pub open spec fn extract_key(tuple: Tuple, cols: Seq<usize>) -> Seq<int>
    decreases cols.len()
{
    if cols.len() == 0 {
        Seq::empty()
    } else {
        let val = tuple.values@[cols[0] as int] as int;
        seq![val].add(extract_key(tuple, cols.subrange(1, cols.len() as int)))
    }
}

// Add tuple to appropriate group (or create new group)
pub open spec fn add_to_groups(tuple: Tuple, key: Seq<int>, groups: Seq<Group>) -> Seq<Group>
    decreases groups.len()
{
    if groups.len() == 0 {
        // Create new group
        seq![Group { key, tuples: seq![tuple] }]
    } else if groups[0].key == key {
        // Add to existing group
        let updated_group = Group {
            key: groups[0].key,
            tuples: groups[0].tuples.push(tuple),
        };
        seq![updated_group].add(groups.subrange(1, groups.len() as int))
    } else {
        // Keep looking
        seq![groups[0]].add(add_to_groups(tuple, key, groups.subrange(1, groups.len() as int)))
    }
}

// Filter groups by HAVING clause (evaluated on group, not individual tuples)
pub open spec fn filter_groups_by_having(groups: Seq<Group>, having: FormulaSpec) -> Seq<Group>
    decreases groups.len()
{
    if groups.len() == 0 {
        Seq::empty()
    } else {
        let rest = filter_groups_by_having(groups.subrange(1, groups.len() as int), having);
        // For HAVING, we need to evaluate on aggregate values
        // Simplified: evaluate on first tuple of group (should be aggregate result)
        if groups[0].tuples.len() > 0 && eval_formula_spec(groups[0].tuples[0], having) {
            seq![groups[0]].add(rest)
        } else {
            rest
        }
    }
}

// Build result tuples from groups by applying aggregates
pub open spec fn build_result_tuples(groups: Seq<Group>, aggs: Seq<AggOp>) -> Bag
    decreases groups.len()
{
    if groups.len() == 0 {
        Seq::empty()
    } else {
        let result_tuple = apply_aggregates(groups[0], aggs);
        seq![result_tuple].add(build_result_tuples(groups.subrange(1, groups.len() as int), aggs))
    }
}

// Apply aggregate operations to a group
// Note: In spec code, we describe the result tuple's properties
#[verifier(external_body)]
pub open spec fn apply_aggregates(group: Group, aggs: Seq<AggOp>) -> Tuple {
    arbitrary()
}

// Axiom describing the aggregate tuple's values
pub open spec fn aggregate_tuple_values(group: Group, aggs: Seq<AggOp>, idx: int) -> Seq<i64>
    decreases aggs.len() - idx
{
    if idx >= aggs.len() {
        Seq::empty()
    } else {
        let agg_val = apply_aggregate(aggs[idx], group) as i64;
        seq![agg_val].add(aggregate_tuple_values(group, aggs, idx + 1))
    }
}

// TODO: Fix spec_fn closure issues
// ===== Adequacy Lemmas - commented out due to spec_fn closure issues =====
/*
// Lemma: SQL Filter satisfies filter specification
pub proof fn filter_is_a_filter_op(instance: Instance, q: Query, formula: FormulaSpec)
    ensures
        is_a_filter_op(
            eval_query(instance, q),
            eval_query(instance, Query::Filter(Box::new(q), formula)),
            |t: Tuple| eval_formula_spec(t, formula)
        )
{
    // Proof by showing nb_occ equality
    admit();
}

// Lemma: SQL GroupBy satisfies grouping specification
pub proof fn groupby_is_a_grouping_op(
    instance: Instance,
    q: Query,
    group_cols: Vec<usize>,
    having: FormulaSpec,
    aggs: Vec<AggOp>
)
    ensures
        is_a_grouping_op(
            eval_query(instance, q),
            eval_query(instance, Query::GroupBy(Box::new(q), group_cols, having, aggs)),
            |input: Bag| partition_by_cols(input, group_cols@),
            |g: Group| eval_formula_spec(g.tuples[0], having), // Simplified
            |g: Group| apply_aggregates(g, aggs@)
        )
{
    // Proof by structural induction
    admit();
}
*/

} // verus!
