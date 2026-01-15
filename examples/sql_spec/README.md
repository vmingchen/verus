# SQL Formal Specification in Verus

This is a Verus adaptation of the Coq formalization from the paper:
**"A Coq formalisation of SQL's execution engines"** by V. Benzaken, E. Contejean, Ch. Keller, and E. Martins (2017)

## Overview

This formalization provides formal specifications and verified implementations for SQL query execution, focusing on:
- **Filter** (WHERE clauses)
- **Group By** (GROUP BY clauses)
- **Aggregate** (COUNT, SUM, AVG, MIN, MAX)

## Architecture

The formalization follows a three-layer architecture:

```
┌─────────────────────────────────────┐
│    High-Level Specification         │  Abstract operator semantics
│    (high_level_spec.rs)            │  using nb_occ (# of occurrences)
└──────────────┬──────────────────────┘
               │
       ┌───────┴────────┐
       │                │
       ▼                ▼
┌──────────────┐  ┌──────────────┐
│   Physical   │  │     SQL      │
│   Algebra    │  │   Algebra    │
│ (Iterator-   │  │ (Relational  │
│   based)     │  │  semantics)  │
└──────┬───────┘  └───────┬──────┘
       │                  │
       └────────┬─────────┘
                │
                ▼
         ┌─────────────┐
         │   Bridge    │  Correctness proofs
         │ (bridge.rs) │
         └─────────────┘
```

### 1. High-Level Specification (`high_level_spec.rs`)

Defines abstract operators using the **number of occurrences** approach:

```rust
pub open spec fn is_a_filter_op<F>(input: Bag, output: Bag, f: F) -> bool
    where F: Fn(Tuple) -> bool
{
    forall |t: Tuple|
        nb_occ(t, output) == nb_occ(t, input) * (if f(t) { 1 } else { 0 })
}
```

**Key Idea**: Two operators are equivalent if they produce bags with the same number of occurrences for every tuple.

### 2. Physical Algebra (`physical_algebra.rs`)

Iterator-based implementation following the "cursor" pattern from database systems:

- **Iterator trait**: Abstract interface with `next()`, `has_next()`, `reset()`
- **SeqScan**: Sequential table scan
- **FilterIter**: On-the-fly filtering
- **GroupByState**: Stateful grouping and aggregation

**Key properties verified**:
- Collection preservation: `self.collection()` remains constant during iteration
- Exhaustiveness: `materialize()` produces all elements from `collection()`
- Termination: Upper bound `ubound()` decreases with each `next()`

### 3. SQL Algebra (`sql_algebra.rs`)

Relational algebra with formal semantics:

```rust
pub enum Query {
    Table(TableName),
    Filter(Box<Query>, Formula),
    GroupBy(Box<Query>, Vec<usize>, Formula, Vec<AggOp>),
}
```

Evaluation function `eval_query` defines the semantics compositionally.

### 4. Bridge (`bridge.rs`)

Correctness proofs showing physical operators implement SQL semantics:

```rust
pub proof fn physical_filter_implements_sql_filter(...)
    ensures
        forall |t: Tuple| {
            nb_occ(t, physical_result) == nb_occ(t, logical_result)
        }
```

## Example Usage

See `sql_spec_example.rs` for a complete example:

```sql
SELECT department, AVG(salary) as avg_salary
FROM employees
WHERE salary > 50000
GROUP BY department
HAVING AVG(salary) > 70000
```

The example shows:
1. Creating sample data
2. Building a query using physical operators
3. Verification that physical execution matches SQL semantics

## Key Differences from Coq Version

### Coq → Verus Adaptations:

| Aspect | Coq | Verus |
|--------|-----|-------|
| **Immutability** | Records return new cursors | Mutable references (`&mut self`) |
| **Result type** | `result A = Result A \| No_Result \| Empty_Cursor` | `enum IterResult { Value(Tuple), NoResult, EmptyCursor }` |
| **Higher-order** | First-class functions | `spec_fn` for ghost, `fn` for exec |
| **Proofs** | Tactics (induction, rewrite) | `proof fn` with `assert`/`assume` |
| **Collections** | Custom finite bags | `Seq<Tuple>` with `nb_occ` |

### Why Verus for SQL Verification?

1. **Separation of spec and impl**: `spec fn` vs regular `fn`
2. **SMT automation**: Many proofs discharge automatically
3. **Executable**: Can run verified code directly
4. **Modern syntax**: Closer to Rust/real implementations

## Verification Strategy

### 1. Specify abstractly using `nb_occ`
```rust
pub open spec fn nb_occ(t: Tuple, bag: Bag) -> nat
```

### 2. Implement with invariants
```rust
fn next(&mut self) -> (result: IterResult)
    ensures
        self.collection() == old(self).collection(),  // Preserved
        match result {
            IterResult::Value(t) =>
                self.visited() == old(self).visited().push(t),
            ...
        }
```

### 3. Prove adequacy
```rust
proof fn filter_is_a_filter_op(...)
    ensures is_a_filter_op(input, output, filter_fn)
```

### 4. Bridge implementations
```rust
proof fn physical_filter_implements_sql_filter(...)
    ensures nb_occ(t, physical) == nb_occ(t, logical)
```

## Future Work

From the paper's perspective section:

- [ ] **Sort-based operators**: Sort-merge join, Sort scan
- [ ] **Hash-based operators**: Hash join, Hash aggregate
- [ ] **Index operations**: Index scan, Bitmap index scan
- [ ] **Nested queries**: Subplan, correlated subqueries
- [ ] **Set operations**: UNION, INTERSECT, EXCEPT
- [ ] **Complete SQL embedding**: Full SQL to algebra translation
- [ ] **Logical optimization**: Prove query rewrite rules
- [ ] **Cost model**: Connect to actual performance

## Building and Running

```bash
# Verify the specifications
cd /Users/ming.chen/github/verus/examples
verus sql_spec_example.rs

# Note: Currently contains admit()s that need full proofs
```

## References

- Original paper: V. Benzaken et al., "A Coq formalisation of SQL's execution engines", ESOP 2017
- Database textbook: Garcia-Molina, Ullman, Widom, "Database Systems: The Complete Book"
- Iterator pattern: Graefe, "Volcano - An Extensible and Parallel Query Evaluation System", IEEE TKDE 1994

## Structure

```
sql_spec/
├── high_level_spec.rs    # Abstract operator specifications
├── physical_algebra.rs   # Iterator-based implementations
├── sql_algebra.rs        # SQL semantics
├── bridge.rs             # Correctness proofs
└── README.md             # This file

sql_spec_example.rs       # Complete example query
```

## Key Insights from the Paper

1. **Pivotal Specification**: A single high-level spec unifies multiple implementations
2. **On-line vs Off-line**: Iterator interface bridges value-at-a-time (exec) and collection-at-a-time (spec)
3. **Invariants are crucial**: `coherent()`, `collection()`, `visited()` maintain correctness
4. **Compositionality**: Prove operators separately, combine via transitivity

## Contact

For questions about this Verus adaptation, please refer to the original paper and Verus documentation.
