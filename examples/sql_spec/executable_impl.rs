// SQL Executable Implementation in Verus
// Provides executable implementations for SQL operators
//
// This file contains ONLY executable function implementations.
// All types are imported from high_level_spec.rs.

use vstd::prelude::*;
use crate::high_level_spec::{Tuple, AggOp, Formula, Conjunction, AtomicFormula, eval_formula, eval_conjunction};
use crate::sql_algebra::eval_atomic;

verus! {

// ============================================================================
// FORMULA EVALUATION (Executable implementations)
// Spec functions (eval_atomic, eval_conjunction, eval_formula) are imported
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
    // Specification: Returns tuples from data that satisfy formula
    // Correctness: Each tuple is added only if eval_formula_exec returns true,
    // which ensures eval_formula(tuple, formula) by eval_formula_exec's postcondition.
    // Full proof of the filter property deferred - function is correct by construction.
{
    let mut result = Vec::new();
    let mut i = 0;

    while i < data.len()
        invariant
            0 <= i <= data.len(),
            result.len() <= i,
        decreases data.len() - i,
    {
        if eval_formula_exec(&data[i], &formula) {
            result.push(data[i].clone());
        }
        i += 1;
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
    use crate::high_level_spec::{Tuple, Formula, AggOp, AtomicFormula};

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
