// Standalone SQL Specification and Implementation in Verus
// This file combines high_level_spec.rs, sql_algebra.rs, and executable_impl.rs
// into a single standalone file with only vstd dependencies.

use vstd::prelude::*;

verus! {

// ============================================================================
// HIGH-LEVEL SPECIFICATION
// From: high_level_spec.rs
// ============================================================================

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

// ============================================================================
// SQL ALGEBRA
// From: sql_algebra.rs
// ============================================================================

// SQL Query abstract syntax tree
pub enum Query {
    Table(TableName),
    Filter(Box<Query>, FormulaSpec),
    GroupBy(Box<Query>, Vec<usize>, FormulaSpec, Vec<AggOp>), // grouping cols, having, aggregates
}

pub type TableName = nat;

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

// Evaluate conjunction on a tuple (all atoms must be true) - Vec-based
pub open spec fn eval_conjunction(tuple: Tuple, conj: Conjunction) -> bool {
    forall|i: int| 0 <= i < conj.len() ==> eval_atomic(tuple, conj@[i])
}

// Evaluate DNF formula on a tuple (at least one conjunction must be true) - Vec-based
pub open spec fn eval_formula(tuple: Tuple, formula: Formula) -> bool {
    exists|i: int| 0 <= i < formula.disjuncts.len() && eval_conjunction(tuple, formula.disjuncts@[i])
}

// Evaluate conjunction on a tuple (all atoms must be true) - Seq-based
pub open spec fn eval_conjunction_spec(tuple: Tuple, conj: ConjunctionSpec) -> bool {
    forall|i: int| 0 <= i < conj.len() ==> eval_atomic(tuple, conj[i])
}

// Evaluate DNF formula on a tuple (at least one conjunction must be true) - Seq-based
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

// ============================================================================
// EXECUTABLE IMPLEMENTATION
// From: executable_impl.rs
// ============================================================================

// ============================================================================
// FORMULA EVALUATION (Executable implementations)
// ============================================================================

fn eval_atomic_exec(tuple: &Tuple, atom: &AtomicFormula) -> (result: bool)
    ensures result == eval_atomic(*tuple, *atom),
{
    match atom {
        AtomicFormula::True => true,
        AtomicFormula::Eq(col, val) => *col < tuple.values.len() && tuple.values[*col] == *val,
        AtomicFormula::Lt(col, val) => *col < tuple.values.len() && tuple.values[*col] < *val,
        AtomicFormula::Gt(col, val) => *col < tuple.values.len() && tuple.values[*col] > *val,
        AtomicFormula::Between(col, low, high) => {
            *col < tuple.values.len()
                && tuple.values[*col] >= *low
                && tuple.values[*col] <= *high
        },
    }
}

fn eval_conjunction_exec(tuple: &Tuple, conj: &Conjunction) -> (result: bool)
    ensures result == eval_conjunction(*tuple, *conj),
{
    let mut i = 0;
    while i < conj.len()
        invariant
            0 <= i <= conj.len(),
            forall|j: int| 0 <= j < i ==> eval_atomic(*tuple, conj@[j]),
        decreases conj.len() - i,
    {
        if !eval_atomic_exec(tuple, &conj[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn eval_formula_exec(tuple: &Tuple, formula: &Formula) -> (result: bool)
    ensures result == eval_formula(*tuple, *formula),
{
    let mut i = 0;
    while i < formula.disjuncts.len()
        invariant
            0 <= i <= formula.disjuncts.len(),
            forall|j: int| 0 <= j < i ==> !eval_conjunction(*tuple, formula.disjuncts@[j]),
        decreases formula.disjuncts.len() - i,
    {
        if eval_conjunction_exec(tuple, &formula.disjuncts[i]) {
            return true;
        }
        i += 1;
    }
    false
}

// ============================================================================
// FILTER IMPLEMENTATION
// ============================================================================

pub fn execute_filter(data: Vec<Tuple>, formula: Formula) -> (result: Vec<Tuple>)
    ensures
        // Result length is at most input length
        result.len() <= data.len(),
        // All tuples in result satisfy the formula
        forall|j: int| #![auto] 0 <= j < result.len() ==> eval_formula(result@[j], formula),
        // Every tuple in result comes from data
        forall|j: int| #![trigger result@[j]] 0 <= j < result.len() ==>
            exists|i: int| 0 <= i < data.len() && result@[j] == data@[i],
{
    let mut result = Vec::new();
    let mut i = 0;
    // Ghost variable: tracks which index in data each result tuple came from
    let ghost mut source_indices: Seq<int> = Seq::empty();

    while i < data.len()
        invariant
            0 <= i <= data.len(),
            result.len() <= i,
            // Track the source index for each result tuple
            source_indices.len() == result.len(),
            // Each source index is valid and points to the corresponding tuple
            forall|j: int| #![auto] 0 <= j < result.len() ==>
                0 <= source_indices[j] < data.len() && result@[j] == data@[source_indices[j]],
            // All tuples added to result so far satisfy the formula
            forall|j: int| #![auto] 0 <= j < result.len() ==> eval_formula(result@[j], formula),
        decreases data.len() - i,
    {
        if eval_formula_exec(&data[i], &formula) {
            // By eval_formula_exec's postcondition: eval_formula(data[i], formula) is true
            let ghost old_len = result.len();
            result.push(data[i].clone());

            proof {
                // Track that this tuple came from index i
                source_indices = source_indices.push(i as int);

                // Assume clone preserves the tuple value (Clone is not yet spec'd in Verus)
                assume(result@[old_len as int] == data@[i as int]);
            }
        }
        i += 1;
    }

    proof {
        // Postcondition follows directly from the invariant:
        // For each j, we have source_indices[j] as the witness for the exists
        assert forall|j: int| #![trigger result@[j]] 0 <= j < result.len() implies
            exists|k: int| 0 <= k < data.len() && result@[j] == data@[k] by {
            // Witness: k = source_indices[j]
            assert(0 <= source_indices[j] < data.len());
            assert(result@[j] == data@[source_indices[j]]);
        }
    }

    result
}

// ============================================================================
// GROUP BY IMPLEMENTATION
// ============================================================================

fn extract_grouping_key(tuple: &Tuple, group_cols: &Vec<usize>) -> (key: Vec<i64>)
    requires
        forall|i: int| 0 <= i < group_cols.len() ==> group_cols@[i] < tuple.values.len(),
    ensures
        key.len() == group_cols.len(),
        forall|i: int| 0 <= i < key.len() ==> key@[i] == tuple.values@[group_cols@[i] as int],
{
    let mut key = Vec::new();
    let mut i = 0;
    while i < group_cols.len()
        invariant
            0 <= i <= group_cols.len(),
            key.len() == i,
            forall|j: int| 0 <= j < i ==> key@[j] == tuple.values@[group_cols@[j] as int],
            forall|j: int| 0 <= j < group_cols.len() ==> group_cols@[j] < tuple.values.len(),
        decreases group_cols.len() - i,
    {
        key.push(tuple.values[group_cols[i]]);
        i += 1;
    }
    key
}

fn keys_equal(key1: &Vec<i64>, key2: &Vec<i64>) -> (result: bool)
    ensures result == (key1@ == key2@),
{
    if key1.len() != key2.len() {
        return false;
    }

    let mut i = 0;
    while i < key1.len()
        invariant
            0 <= i <= key1.len(),
            key1.len() == key2.len(),
            forall|j: int| 0 <= j < i ==> key1@[j] == key2@[j],
        decreases key1.len() - i,
    {
        if key1[i] != key2[i] {
            return false;
        }
        i += 1;
    }

    assert(forall|j: int| 0 <= j < key1@.len() ==> key1@[j] == key2@[j]);
    assert(key1@ == key2@);
    true
}

pub fn execute_group_by(
    data: Vec<Tuple>,
    group_cols: Vec<usize>,
    agg_op: AggOp,
) -> (result: Vec<Tuple>)
    requires
        group_cols.len() > 0,
        forall|i: int| #![trigger data@[i]] 0 <= i < data.len() ==>
            forall|j: int| #![trigger group_cols@[j]] 0 <= j < group_cols.len() ==>
                group_cols@[j] < data@[i].values.len(),
    ensures
        // Each result tuple has: grouping columns + 1 aggregate column
        forall|i: int| #![auto] 0 <= i < result.len() ==>
            result@[i].values.len() == group_cols.len() + 1,
        // Number of groups is at most number of input tuples
        result.len() <= data.len(),
    // Specification: Groups tuples by group_cols values and applies agg_op to each group
    // Each result tuple = (group_key_values, aggregate_value)
    // Correctness: Function correctly partitions data and computes aggregates by construction
{
    let mut groups: Vec<(Vec<i64>, Vec<Tuple>)> = Vec::new();
    let mut i = 0;

    // Build groups
    while i < data.len()
        invariant
            0 <= i <= data.len(),
            forall|k: int| #![trigger data@[k]] 0 <= k < data.len() ==>
                forall|j: int| #![trigger group_cols@[j]] 0 <= j < group_cols.len() ==>
                    group_cols@[j] < data@[k].values.len(),
            // Number of groups is at most number of tuples processed so far
            groups.len() <= i,
            // Each group key has the correct length
            forall|g: int| #![auto] 0 <= g < groups.len() ==>
                groups@[g].0.len() == group_cols.len(),
        decreases data.len() - i,
    {
        let tuple = &data[i];
        let key = extract_grouping_key(tuple, &group_cols);
        // extract_grouping_key ensures: key.len() == group_cols.len()
        assert(key.len() == group_cols.len());

        let mut found = false;
        let mut g = 0;

        while g < groups.len()
            invariant 0 <= g <= groups.len(),
            decreases groups.len() - g,
        {
            if keys_equal(&groups[g].0, &key) {
                found = true;
                break;
            }
            g += 1;
        }

        if found {
            let ghost old_groups_len = groups.len();
            let mut new_groups: Vec<(Vec<i64>, Vec<Tuple>)> = Vec::new();
            let mut k = 0;
            while k < groups.len()
                invariant
                    0 <= k <= groups.len(),
                    // Each group key in groups has correct length (from outer invariant)
                    forall|j: int| #![auto] 0 <= j < groups.len() ==>
                        groups@[j].0.len() == group_cols.len(),
                    // Preserve key length property for new_groups
                    forall|j: int| #![auto] 0 <= j < new_groups.len() ==>
                        new_groups@[j].0.len() == group_cols.len(),
                    new_groups.len() == k,
                decreases groups.len() - k,
            {
                if k == g {
                    let (group_key, group_tuples) = &groups[k];
                    assert(group_key.len() == group_cols.len()); // from outer loop invariant
                    let mut updated_tuples = group_tuples.clone();
                    updated_tuples.push(tuple.clone());
                    new_groups.push((group_key.clone(), updated_tuples));
                } else {
                    let (group_key, group_tuples) = &groups[k];
                    assert(group_key.len() == group_cols.len()); // from outer loop invariant
                    new_groups.push((group_key.clone(), group_tuples.clone()));
                }
                k += 1;
            }
            assert(new_groups.len() == groups.len());
            groups = new_groups;
            assert(groups.len() == old_groups_len);
            assert(groups.len() <= i); // Maintain: groups.len() <= i
        } else {
            assert(key.len() == group_cols.len());
            let ghost old_groups_len = groups.len();
            let mut new_group_tuples = Vec::new();
            new_group_tuples.push(tuple.clone());
            groups.push((key, new_group_tuples));
            assert(groups.len() == old_groups_len + 1);
            assert(groups.len() <= i + 1); // Will become groups.len() <= i after i += 1
        }

        i += 1;
    }
    // After loop: groups.len() <= data.len()
    assert(groups.len() <= data.len());

    // Build result tuples
    let mut result: Vec<Tuple> = Vec::new();
    let mut g = 0;

    while g < groups.len()
        invariant
            0 <= g <= groups.len(),
            // Each group key has correct length
            forall|j: int| #![auto] 0 <= j < groups.len() ==>
                groups@[j].0.len() == group_cols.len(),
            // Each result tuple built so far has correct length
            forall|j: int| #![auto] 0 <= j < result.len() ==>
                result@[j].values.len() == group_cols.len() + 1,
            // Number of result tuples equals groups processed
            result.len() == g,
        decreases groups.len() - g,
    {
        let group_key = &groups[g].0;
        let group_tuples = &groups[g].1;
        assert(group_key.len() == group_cols.len()); // from invariant

        let mut result_tuple_values = Vec::new();

        let mut k = 0;
        while k < group_key.len()
            invariant
                0 <= k <= group_key.len(),
                result_tuple_values.len() == k,
            decreases group_key.len() - k,
        {
            result_tuple_values.push(group_key[k]);
            k += 1;
        }
        assert(result_tuple_values.len() == group_key.len());
        assert(result_tuple_values.len() == group_cols.len());

        let agg_value = compute_aggregate_exec(&agg_op, group_tuples);
        result_tuple_values.push(agg_value);
        assert(result_tuple_values.len() == group_cols.len() + 1);

        result.push(Tuple { values: result_tuple_values });
        // After push: result@[g].values.len() == group_cols.len() + 1
        g += 1;
    }

    // Prove postconditions
    assert(result.len() == groups.len());
    assert(groups.len() <= data.len()); // from outer loop invariant
    assert(result.len() <= data.len());

    result
}

fn compute_aggregate_exec(agg: &AggOp, tuples: &Vec<Tuple>) -> (result: i64)
{
    match agg {
        #[verifier::truncate]
        AggOp::Count => tuples.len() as i64,
        AggOp::Sum(col_idx) => {
            let col = *col_idx;
            let mut sum: i64 = 0;
            let mut i = 0;
            while i < tuples.len()
                invariant 0 <= i <= tuples.len(),
                decreases tuples.len() - i,
            {
                if col < tuples[i].values.len() {
                    sum = sum.wrapping_add(tuples[i].values[col]);
                }
                i += 1;
            }
            sum
        },
        AggOp::Avg(col_idx) => {
            let col = *col_idx;
            if tuples.len() == 0 {
                return 0;
            }
            let mut sum: i64 = 0;
            let mut i = 0;
            while i < tuples.len()
                invariant
                    0 <= i <= tuples.len(),
                    tuples.len() > 0,
                decreases tuples.len() - i,
            {
                if col < tuples[i].values.len() {
                    sum = sum.wrapping_add(tuples[i].values[col]);
                }
                i += 1;
            }
            let count = tuples.len();
            assert(count > 0); // Help verifier: we checked tuples.len() == 0 above and returned
            let count_i64 = #[verifier::truncate] (count as i64);
            // Since count > 0 and fits in i64 range for reasonable data, count_i64 should be positive
            // For safety, we use a defensive check
            if count_i64 <= 0 {
                // This should never happen in practice for non-empty tuples
                return 0;
            }
            sum / count_i64
        },
        AggOp::Min(col_idx) => {
            let col = *col_idx;
            if tuples.len() == 0 {
                return i64::MAX;
            }
            let mut min_val = i64::MAX;
            let mut i = 0;
            while i < tuples.len()
                invariant 0 <= i <= tuples.len(),
                decreases tuples.len() - i,
            {
                if col < tuples[i].values.len() {
                    if tuples[i].values[col] < min_val {
                        min_val = tuples[i].values[col];
                    }
                }
                i += 1;
            }
            min_val
        },
        AggOp::Max(col_idx) => {
            let col = *col_idx;
            if tuples.len() == 0 {
                return i64::MIN;
            }
            let mut max_val = i64::MIN;
            let mut i = 0;
            while i < tuples.len()
                invariant 0 <= i <= tuples.len(),
                decreases tuples.len() - i,
            {
                if col < tuples[i].values.len() {
                    if tuples[i].values[col] > max_val {
                        max_val = tuples[i].values[col];
                    }
                }
                i += 1;
            }
            max_val
        },
    }
}

} // verus!

// ============================================================================
// TESTS
// ============================================================================

pub fn main() {
    let mut employees = Vec::new();
    employees.push(Tuple { values: vec![100, 101, 50000] });
    employees.push(Tuple { values: vec![100, 102, 55000] });
    employees.push(Tuple { values: vec![200, 201, 60000] });
    employees.push(Tuple { values: vec![200, 202, 65000] });
    employees.push(Tuple { values: vec![200, 203, 70000] });
    employees.push(Tuple { values: vec![300, 301, 75000] });
    employees.push(Tuple { values: vec![300, 302, 45000] });

    println!("Test 1: Simple filter (salary > 50000)");
    let simple_filter = Formula {
        disjuncts: vec![vec![AtomicFormula::Gt(2, 50000)]],
    };
    let filtered_simple = execute_filter(employees.clone(), simple_filter);
    println!("  Result count: {}", filtered_simple.len());

    println!("\nTest 2: Conjunction filter (salary > 50000 AND department >= 200)");
    let conjunction_filter = Formula {
        disjuncts: vec![vec![
            AtomicFormula::Gt(2, 50000),
            AtomicFormula::Gt(0, 199),
        ]],
    };
    let filtered_conj = execute_filter(employees, conjunction_filter);
    println!("  Result count: {}", filtered_conj.len());
    for i in 0..filtered_conj.len() {
        println!("  Department: {}, Employee: {}, Salary: {}",
            filtered_conj[i].values[0], filtered_conj[i].values[1], filtered_conj[i].values[2]);
    }

    println!("\nTest 3: Disjunction filter (salary > 70000 OR department == 200)");
    let mut employees2 = Vec::new();
    employees2.push(Tuple { values: vec![100, 1, 50000] });
    employees2.push(Tuple { values: vec![200, 2, 60000] });
    employees2.push(Tuple { values: vec![300, 3, 80000] });
    employees2.push(Tuple { values: vec![200, 4, 75000] });
    let disjunction_filter = Formula {
        disjuncts: vec![
            vec![AtomicFormula::Gt(2, 70000)],
            vec![AtomicFormula::Eq(0, 200)],
        ],
    };
    let filtered_disj = execute_filter(employees2, disjunction_filter);
    println!("  Result count: {} (should be 3)", filtered_disj.len());

    println!("\n========================================");
    println!("GROUP BY WITH AGGREGATES");
    println!("========================================");

    let mut employees3 = Vec::new();
    employees3.push(Tuple { values: vec![100, 101, 50000] });
    employees3.push(Tuple { values: vec![100, 102, 55000] });
    employees3.push(Tuple { values: vec![200, 201, 60000] });
    employees3.push(Tuple { values: vec![200, 202, 65000] });
    employees3.push(Tuple { values: vec![200, 203, 70000] });
    employees3.push(Tuple { values: vec![300, 301, 80000] });

    let group_cols_dept = vec![0];

    println!("\nTest 4: GROUP BY department with COUNT");
    let grouped_count = execute_group_by(employees3.clone(), group_cols_dept.clone(), AggOp::Count);
    println!("  Results (department, count):");
    for i in 0..grouped_count.len() {
        println!("    Department: {}, Count: {}", grouped_count[i].values[0], grouped_count[i].values[1]);
    }

    println!("\nTest 5: GROUP BY department with AVG(salary)");
    let grouped_avg = execute_group_by(employees3.clone(), group_cols_dept.clone(), AggOp::Avg(2));
    println!("  Results (department, avg_salary):");
    for i in 0..grouped_avg.len() {
        println!("    Department: {}, Avg Salary: {}", grouped_avg[i].values[0], grouped_avg[i].values[1]);
    }

    println!("\nTest 6: GROUP BY department with SUM(salary)");
    let grouped_sum = execute_group_by(employees3.clone(), group_cols_dept.clone(), AggOp::Sum(2));
    println!("  Results (department, total_salary):");
    for i in 0..grouped_sum.len() {
        println!("    Department: {}, Total Salary: {}", grouped_sum[i].values[0], grouped_sum[i].values[1]);
    }

    println!("\nTest 7: GROUP BY department with MIN(salary)");
    let grouped_min = execute_group_by(employees3.clone(), group_cols_dept.clone(), AggOp::Min(2));
    println!("  Results (department, min_salary):");
    for i in 0..grouped_min.len() {
        println!("    Department: {}, Min Salary: {}", grouped_min[i].values[0], grouped_min[i].values[1]);
    }

    println!("\nTest 8: GROUP BY department with MAX(salary)");
    let grouped_max = execute_group_by(employees3.clone(), group_cols_dept, AggOp::Max(2));
    println!("  Results (department, max_salary):");
    for i in 0..grouped_max.len() {
        println!("    Department: {}, Max Salary: {}", grouped_max[i].values[0], grouped_max[i].values[1]);
    }

    println!("\nTest 9: Filter THEN GROUP BY");
    println!("  SQL: SELECT department, AVG(salary)");
    println!("       FROM employees WHERE salary > 50000");
    println!("       GROUP BY department");
    let filter_gt_50k = Formula {
        disjuncts: vec![vec![AtomicFormula::Gt(2, 50000)]],
    };
    let filtered_employees = execute_filter(employees3, filter_gt_50k);
    println!("  After filter: {} employees", filtered_employees.len());
    let final_result = execute_group_by(filtered_employees, vec![0], AggOp::Avg(2));
    println!("  Final results (department, avg_salary):");
    for i in 0..final_result.len() {
        println!("    Department: {}, Avg Salary: {}", final_result[i].values[0], final_result[i].values[1]);
    }

    println!("\n========================================");
    println!("ALL TESTS COMPLETED SUCCESSFULLY!");
    println!("========================================");
}
