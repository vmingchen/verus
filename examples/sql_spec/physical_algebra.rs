// Physical Algebra: Iterator-based implementation
// Based on Section 4 of the SQL formalization paper

use vstd::prelude::*;
use crate::high_level_spec::*;

verus! {

// Iterator result - similar to Coq's result type
pub enum IterResult {
    Value(Tuple),      // Successfully returned a tuple
    NoResult,          // Filtered out by condition
    EmptyCursor,       // Iterator exhausted
}

// Abstract iterator trait specification
// This captures the essence of the Cursor record from the paper
pub trait Iterator {
    // Ghost function: all elements this iterator will produce
    spec fn collection(&self) -> Bag;

    // Ghost function: elements already visited
    spec fn visited(&self) -> Bag;

    // Ghost function: invariant that must be maintained
    spec fn coherent(&self) -> bool;

    // Ghost function: upper bound on remaining iterations
    spec fn ubound(&self) -> nat;

    // Check if there are more elements
    fn has_next(&self) -> (result: bool)
        requires self.coherent()
        ensures result == (self.ubound() > 0);

    // Get next element (mutates the iterator)
    fn next(&mut self) -> (result: IterResult)
        requires old(self).coherent()
        ensures
            self.coherent(),
            // Collection is preserved
            self.collection() == old(self).collection(),
            // Visited is updated appropriately
            match result {
                IterResult::Value(t) => {
                    self.visited() == old(self).visited().push(t) &&
                    nb_occ(t, old(self).collection()) > 0
                },
                IterResult::NoResult => {
                    self.visited() == old(self).visited()
                },
                IterResult::EmptyCursor => {
                    self.visited() == old(self).visited() &&
                    self.ubound() == 0
                },
            };

    // Reset iterator to beginning
    fn reset(&mut self)
        ensures
            self.collection() == old(self).collection(),
            self.visited().len() == 0,
            self.coherent();
}

// Sequential scan iterator - base implementation
pub struct SeqScan {
    pub data: Vec<Tuple>,      // All tuples in the relation
    pub position: usize,        // Current position
    pub ghost collection_view: Bag,
}

impl SeqScan {
    pub fn new(data: Vec<Tuple>) -> (result: Self)
        ensures
            result.coherent(),
            result.collection() == data@,
            result.visited().len() == 0,
    {
        SeqScan {
            collection_view: Ghost(data@),
            data,
            position: 0,
        }
    }
}

impl Iterator for SeqScan {
    closed spec fn collection(&self) -> Bag {
        self.data@
    }

    closed spec fn visited(&self) -> Bag {
        self.data@.subrange(0, self.position as int)
    }

    closed spec fn coherent(&self) -> bool {
        self.position <= self.data.len() &&
        self.collection() == self.data@
    }

    closed spec fn ubound(&self) -> nat {
        (self.data.len() - self.position) as nat
    }

    fn has_next(&self) -> (result: bool) {
        self.position < self.data.len()
    }

    fn next(&mut self) -> (result: IterResult) {
        if self.position < self.data.len() {
            let tuple = self.data[self.position].clone();
            self.position += 1;
            IterResult::Value(tuple)
        } else {
            IterResult::EmptyCursor
        }
    }

    fn reset(&mut self) {
        self.position = 0;
    }
}

// Filter iterator - wraps another iterator
pub struct FilterIter<I: Iterator> {
    pub inner: I,
    pub filter_fn: spec_fn(Tuple) -> bool, // Ghost filter function
    pub filter_impl: fn(&Tuple) -> bool,   // Executable filter
}

impl<I: Iterator> Iterator for FilterIter<I> {
    closed spec fn collection(&self) -> Bag {
        filter_bag(self.inner.collection(), self.filter_fn)
    }

    closed spec fn visited(&self) -> Bag {
        filter_bag(self.inner.visited(), self.filter_fn)
    }

    closed spec fn coherent(&self) -> bool {
        self.inner.coherent() &&
        // Filter function must match implementation
        (forall |t: Tuple| (#[trigger] self.filter_fn)(t) == (self.filter_impl)(&t))
    }

    closed spec fn ubound(&self) -> nat {
        self.inner.ubound()
    }

    fn has_next(&self) -> (result: bool) {
        self.inner.has_next()
    }

    fn next(&mut self) -> (result: IterResult) {
        match self.inner.next() {
            IterResult::Value(t) => {
                if (self.filter_impl)(&t) {
                    IterResult::Value(t)
                } else {
                    IterResult::NoResult
                }
            },
            IterResult::NoResult => IterResult::NoResult,
            IterResult::EmptyCursor => IterResult::EmptyCursor,
        }
    }

    fn reset(&mut self) {
        self.inner.reset()
    }
}

// Helper: filter a bag according to a predicate
pub open spec fn filter_bag(bag: Bag, f: spec_fn(Tuple) -> bool) -> Bag
    decreases bag.len()
{
    if bag.len() == 0 {
        Seq::empty()
    } else {
        let rest = filter_bag(bag.subrange(1, bag.len() as int), f);
        if f(bag[0]) {
            seq![bag[0]].add(rest)
        } else {
            rest
        }
    }
}

// Materialize: exhaust iterator and collect all results
pub fn materialize<I: Iterator>(iter: &mut I) -> (result: Vec<Tuple>)
    requires old(iter).coherent()
    ensures
        iter.coherent(),
        // All elements from collection are in result
        forall |t: Tuple| nb_occ(t, result@) == nb_occ(t, old(iter).collection()),
{
    let mut results = Vec::new();
    let ghost orig_collection = iter.collection();

    iter.reset();

    loop
        invariant
            iter.coherent(),
            iter.collection() == orig_collection,
            // Results collected so far match visited elements
            forall |t: Tuple| nb_occ(t, results@) == nb_occ(t, iter.visited()),
    {
        match iter.next() {
            IterResult::Value(t) => {
                results.push(t);
            },
            IterResult::NoResult => {
                // Skip filtered elements
            },
            IterResult::EmptyCursor => {
                break;
            },
        }
    }

    results
}

// Group-by state for aggregation
pub struct GroupByState {
    pub groups: Vec<Group>,
    pub group_keys: Vec<Seq<int>>,
}

impl GroupByState {
    pub fn new() -> (result: Self)
        ensures result.groups@.len() == 0
    {
        GroupByState {
            groups: Vec::new(),
            group_keys: Vec::new(),
        }
    }

    // Find or create a group for the given key
    pub fn find_or_create_group(&mut self, key: Seq<int>) -> (idx: usize)
        ensures
            idx < self.groups.len(),
            self.groups[idx as int].key == key,
    {
        // Search for existing group
        let mut i = 0;
        while i < self.group_keys.len()
            invariant
                i <= self.group_keys.len(),
                self.group_keys.len() == self.groups.len(),
        {
            if self.group_keys[i] == key {
                return i;
            }
            i += 1;
        }

        // Create new group
        let new_group = Group {
            key,
            tuples: Seq::empty(),
        };
        self.groups.push(new_group);
        self.group_keys.push(key);

        self.groups.len() - 1
    }

    // Add tuple to a group
    pub fn add_to_group(&mut self, group_idx: usize, tuple: Tuple)
        requires
            group_idx < old(self).groups.len(),
        ensures
            self.groups.len() == old(self).groups.len(),
            self.groups[group_idx as int].tuples ==
                old(self).groups[group_idx as int].tuples.push(tuple),
    {
        let group = &mut self.groups[group_idx];
        let new_tuples = group.tuples.push(tuple);
        group.tuples = new_tuples;
    }
}

} // verus!

// Helper: filter a bag (specification)
pub open spec fn filter_bag(bag: Bag, f: spec_fn(Tuple) -> bool) -> Bag;
