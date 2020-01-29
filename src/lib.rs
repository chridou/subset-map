//! # subset-map
//!
//! ## Summary
//!
//! `subset-map` is a map like data structure where the keys are combinations
//! of elements the `SubsetMap` has been initialized with.
//!
//! The order of the elements is defined by the position of an element
//! within the elements the `SubsetMap` has been initialized with.
//!
//! `SubsetMap` clones the elements into the subsets. So you should
//! consider to only use element types where you would feel good to assign
//! them the `Copy` trait.
//!
//! Lookup is done linearly. Therefore `SubsetMap` should only be used
//! with not too big sets of elements.
//!
//! ### Example
//!
//! ```
//! use subset_map::*;
//! // Initialize the map where the payloads are basically the keys
//! let subset_map = SubsetMap::fill(&[1, 2, 3], |x| x.iter().cloned().collect::<Vec<_>>());
//!
//! assert_eq!(subset_map.get(&[1]), Some(&vec![1]));
//! assert_eq!(subset_map.get(&[2]), Some(&vec![2]));
//! assert_eq!(subset_map.get(&[3]), Some(&vec![3]));
//! assert_eq!(subset_map.get(&[1, 2]), Some(&vec![1, 2]));
//! assert_eq!(subset_map.get(&[2, 3]), Some(&vec![2, 3]));
//! assert_eq!(subset_map.get(&[1, 3]), Some(&vec![1, 3]));
//! assert_eq!(subset_map.get(&[1, 2, 3]), Some(&vec![1, 2, 3]));
//!
//! // No internal ordering is performed:
//! // The position in the original set is crucial:
//! assert_eq!(subset_map.get(&[2,1]), None);
//! ```
//!
//! ## Features
//!
//! The `serde` feature allows serialization and deserialization with `serde`.
//!
//! ## Recent Changes
//!
//! * 0.3.2
//!     * Added more methods to iterate/walk
//! * 0.3.1
//!     * Added methods to work with payloads
//! * 0.3.0
//!     * [BREAKING CHANGES]: Changed API to be more consistent
//! * 0.2.2
//!     * fixed `size` function
//! * 0.2.1
//!     * Optimized `find` and `lookup` a bit
//!     * Added `size` finction to return the number of combinations
//! * 0.2.0
//!     * Renamed MatchQuality to `LookupResult`
//!     * `LookupResult` also contains the no match case
//!     * improved documentation
//!
//! ## License
//!
//! `subset-map` is distributed under the terms of both the MIT license and the Apache License (Version
//! 2.0).
//!
//! Copyright(2018) Christian Douven
//!
//! See LICENSE-APACHE and LICENSE-MIT for details.
#[cfg(feature = "serde")]
#[macro_use]
extern crate serde;

type Nodes<I, P> = Vec<SubsetMapNode<I, P>>;

/// A map like data structure where the keys are subsets made of
/// combinations of the original sets.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct SubsetMap<E, P> {
    nodes: Nodes<E, P>,
}

impl<E, P> SubsetMap<E, P>
where
    E: Clone,
{
    /// Creates a new instance where the payloads are
    /// initialized with a closure that is passed the
    /// current subset of elements.
    ///
    /// This function assigns values to those combinations where
    /// the given closure `init` returns `Some`.
    ///
    /// # Example
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::new(&[1, 2], |x| {
    ///     let sum = x.iter().sum::<i32>();
    ///     if sum == 1 {
    ///         None
    ///     } else {
    ///         Some(sum)
    ///     }
    /// });
    ///
    /// assert_eq!(subset_map.get(&[1]), None);
    /// assert_eq!(subset_map.get(&[2]), Some(&2));
    /// assert_eq!(subset_map.get(&[1, 2]), Some(&3));
    /// assert_eq!(subset_map.get(&[]), None);
    /// assert_eq!(subset_map.get(&[2, 1]), None);
    /// assert_eq!(subset_map.get(&[0]), None);
    /// assert_eq!(subset_map.get(&[0, 1]), None);
    /// ```
    pub fn new<F>(elements: &[E], mut init: F) -> SubsetMap<E, P>
    where
        F: FnMut(&[E]) -> Option<P>,
    {
        init_root::<_, _, _, ()>(elements, &mut |elements| Ok(init(elements))).unwrap()
    }

    /// Creates a new instance where the payloads are
    /// initialized with a closure that is passed the
    /// current subset of elements.
    ///
    /// This fuction will assign an element to each subset.
    ///
    /// # Example
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::fill(&[1, 2], |x| x.iter().sum::<i32>());
    /// assert_eq!(subset_map.get(&[1]), Some(&1));
    /// assert_eq!(subset_map.get(&[2]), Some(&2));
    /// assert_eq!(subset_map.get(&[1, 2]), Some(&3));
    /// assert_eq!(subset_map.get(&[]), None);
    /// assert_eq!(subset_map.get(&[2, 1]), None);
    /// assert_eq!(subset_map.get(&[0]), None);
    /// assert_eq!(subset_map.get(&[0, 1]), None);
    /// ```
    pub fn fill<F>(elements: &[E], mut init: F) -> SubsetMap<E, P>
    where
        F: FnMut(&[E]) -> P,
    {
        init_root::<_, _, _, ()>(elements, &mut |elements| Ok(Some(init(elements)))).unwrap()
    }

    /// Initializes the `SubsetMap` with a closure that can fail.
    /// This function initializes all those subsets with the returned payloads
    /// where the `init` closure returned an `Result::Ok(Option::Some)`
    /// given that all calls on the closure returned `Result::Ok`.
    ///
    /// Failure of the `init` closure will result in a failure
    /// of the whole initialization process.
    ///
    /// # Example
    ///
    /// The whole initialization process fails.
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::init(&[1, 2], |x| {
    ///     let sum = x.iter().sum::<i32>();
    ///     if sum == 1 {
    ///         Ok(Some(sum))
    ///     } else if sum == 2 {
    ///         Ok(None)
    ///     } else {
    ///         Err("bang!")
    ///     }
    /// });
    ///
    /// assert_eq!(subset_map, Err("bang!"));
    /// ```
    pub fn init<F, X>(elements: &[E], mut init: F) -> Result<SubsetMap<E, P>, X>
    where
        F: FnMut(&[E]) -> Result<Option<P>, X>,
    {
        init_root(elements, &mut init)
    }

    /// Initializes the `SubsetMap` with a closure that can fail.
    /// This function initializes all subsets with the returned payloads
    /// given that all calls on the closure returned `Result::Ok`.
    ///
    /// Failure of the `init` closure will result in a failure
    /// of the whole initialization process.
    ///
    /// # Example
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::init_filled(&[1, 2], |x| {
    ///     let sum = x.iter().sum::<i32>();
    ///     if sum != 3 {
    ///         Ok(sum)
    ///     } else {
    ///         Err("bang!")
    ///     }
    /// });
    ///
    /// assert_eq!(subset_map, Err("bang!"));
    /// ```
    pub fn init_filled<F, X>(elements: &[E], mut init: F) -> Result<SubsetMap<E, P>, X>
    where
        F: FnMut(&[E]) -> Result<P, X>,
    {
        init_root::<_, _, _, X>(elements, &mut |elements| init(elements).map(Some))
    }

    /// Creates a new instance where the payloads are all initialized
    /// with the same value.
    ///
    /// # Example
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::with_value(&[1, 2], || 42);
    /// assert_eq!(subset_map.get(&[1]), Some(&42));
    /// assert_eq!(subset_map.get(&[2]), Some(&42));
    /// assert_eq!(subset_map.get(&[1, 2]), Some(&42));
    /// assert_eq!(subset_map.get(&[]), None);
    /// assert_eq!(subset_map.get(&[2, 1]), None);
    /// assert_eq!(subset_map.get(&[0]), None);
    /// assert_eq!(subset_map.get(&[0, 1]), None);
    /// ```
    pub fn with_value<F>(elements: &[E], mut init: F) -> SubsetMap<E, P>
    where
        F: FnMut() -> P,
    {
        init_root::<_, _, _, ()>(elements, &mut |_| Ok(Some(init()))).unwrap()
    }

    /// Creates a new instance where the payloads are all initialized
    /// with the `Default::default()` value of the payload type.
    /// Creates a new instance where the payloads are all initialized
    /// with the same value.
    ///
    /// # Example
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::with_default(&[1, 2]);
    /// assert_eq!(subset_map.get(&[1]), Some(&0));
    /// assert_eq!(subset_map.get(&[2]), Some(&0));
    /// assert_eq!(subset_map.get(&[1, 2]), Some(&0));
    /// assert_eq!(subset_map.get(&[]), None);
    /// assert_eq!(subset_map.get(&[2, 1]), None);
    /// assert_eq!(subset_map.get(&[0]), None);
    /// assert_eq!(subset_map.get(&[0, 1]), None);
    /// ```
    pub fn with_default(elements: &[E]) -> SubsetMap<E, P>
    where
        P: Default,
    {
        init_root::<_, _, _, ()>(elements, &mut |_| Ok(Some(P::default()))).unwrap()
    }

    /// Gets a payload by the given subset.
    ///
    /// Only "perfect" matches on `subset` are returned.
    ///
    /// The function returns `None` regardless of whether
    /// `subset` was part of the map or there was no payload
    /// assigned to the given subset.
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::new(&[1, 2, 3], |x| {
    ///     let payload = x.iter().cloned().collect::<Vec<_>>();
    ///     if payload.len() == 1 {
    ///         None
    ///     } else {
    ///         Some(payload)
    ///     }
    /// });
    /// assert_eq!(subset_map.get(&[1]), None);
    /// assert_eq!(subset_map.get(&[2]), None);
    /// assert_eq!(subset_map.get(&[3]), None);
    /// assert_eq!(subset_map.get(&[1, 2]), Some(&vec![1, 2]));
    /// assert_eq!(subset_map.get(&[2, 3]), Some(&vec![2, 3]));
    /// assert_eq!(subset_map.get(&[1, 3]), Some(&vec![1, 3]));
    /// assert_eq!(subset_map.get(&[1, 2, 3]), Some(&vec![1, 2, 3]));
    ///
    /// assert_eq!(subset_map.get(&[]), None);
    /// assert_eq!(subset_map.get(&[7]), None);
    /// assert_eq!(subset_map.get(&[3, 2, 1]), None);
    /// assert_eq!(subset_map.get(&[1, 3, 2]), None);
    /// assert_eq!(subset_map.get(&[3, 2, 1]), None);
    /// assert_eq!(subset_map.get(&[2, 1]), None);
    /// ```
    pub fn get<'a>(&'a self, subset: &[E]) -> Option<&'a P>
    where
        E: Eq,
    {
        get(subset, &self.nodes)
    }

    /// Looks up a payload by the given subset and returns the
    /// corresponding owned value.
    ///
    /// The function returns `None` regardless of wether
    /// `subset` was part of the map or there was no payload
    /// assigned to the given subset.
    ///
    /// Only perfect matches on `subset` are returned. See `get`.
    pub fn get_owned(&self, subset: &[E]) -> Option<P::Owned>
    where
        E: Eq,
        P: ToOwned,
    {
        get(subset, &self.nodes).map(|p| p.to_owned())
    }

    /// Looks up a subset and maybe returns the assigned payload.
    ///
    /// Elements in `subset` that are not part of the initial set are
    /// skipped.
    ///
    /// The returned `LookupResult` may still contain an optional
    /// payload. None indicates that the subset was matched but
    /// there was no payload for the given subset.
    ///
    /// Use this method if you are interested whether there was
    /// a matching subset and then process the maybe present payload.
    /// Otherwise use `find` or `lookup`.
    ///
    /// # Example
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::new(&[1u32, 2, 3], |x| {
    ///     if x == &[2] {
    ///         None
    ///     } else {
    ///         let payload = x.iter().cloned().collect::<Vec<_>>();
    ///         Some(payload)
    ///     }
    /// });
    ///
    /// let empty: &[u32] = &[];
    ///
    /// // A perfect match with a payload:
    /// let match_result = subset_map.lookup(&[1]);
    /// assert_eq!(match_result.payload(), Some(&vec![1]));
    /// assert_eq!(match_result.excluded_elements(), empty);
    /// assert_eq!(match_result.is_match(), true);
    /// assert_eq!(match_result.is_perfect(), true);
    /// assert_eq!(match_result.is_excluded(), false);
    ///
    /// // A perfect match that has no payload:
    /// let match_result = subset_map.lookup(&[2]);
    /// assert_eq!(match_result.payload(), None);
    /// assert_eq!(match_result.excluded_elements(), empty);
    /// assert_eq!(match_result.is_match(), true);
    /// assert_eq!(match_result.is_perfect(), true);
    /// assert_eq!(match_result.is_excluded(), false);
    ///
    /// // There is no answer at all:
    /// let match_result = subset_map.lookup(&[42]);
    /// assert_eq!(match_result.is_no_match(), true);
    /// assert_eq!(match_result.is_perfect(), false);
    /// assert_eq!(match_result.is_excluded(), false);
    /// assert_eq!(match_result.excluded_elements(), empty);
    ///
    /// // A nearby match but that has a payload:
    /// let match_result = subset_map.lookup(&[3,1]);
    /// assert_eq!(match_result.payload(), Some(&vec![3]));
    /// assert_eq!(match_result.excluded_elements(), &[1]);
    /// assert_eq!(match_result.is_perfect(), false);
    /// assert_eq!(match_result.is_excluded(), true);
    /// assert_eq!(match_result.is_match(), true);
    ///
    /// ```
    pub fn lookup<'a>(&'a self, subset: &[E]) -> LookupResult<'a, E, P>
    where
        E: Eq,
    {
        lookup(subset, &self.nodes)
    }

    /// Finds a payload by the given subset.
    ///
    /// Elements in `subset` that are not part of the initial set are
    /// skipped.
    ///
    /// If there was no match or no payload for the given subset
    /// `FindResult::NotFound` is returned.
    ///
    /// Use this function if you are mostly interested in
    /// payloads and how they were matched. Otherwise
    /// use `lookup` or `get`
    ///
    /// # Example
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::new(&[1u32, 2, 3], |x| {
    ///     if x == &[2] {
    ///         None
    ///     } else {
    ///         let payload = x.iter().cloned().collect::<Vec<_>>();
    ///         Some(payload)
    ///     }
    /// });
    ///
    /// let empty: &[u32] = &[];
    ///
    /// // A perfect match with a payload:
    /// let match_result = subset_map.find(&[1]);
    ///
    /// assert_eq!(match_result.payload(), Some(&vec![1]));
    /// assert_eq!(match_result.is_found(), true);
    /// assert_eq!(match_result.is_found_and_perfect(), true);
    /// assert_eq!(match_result.is_found_and_excluded(), false);
    /// assert_eq!(match_result.excluded_elements(), empty);
    ///
    /// // A perfect match that has no payload:
    /// let match_result = subset_map.find(&[2]);
    ///
    /// assert_eq!(match_result.payload(), None);
    /// assert_eq!(match_result.is_found(), false);
    /// assert_eq!(match_result.is_found_and_perfect(), false);
    /// assert_eq!(match_result.is_found_and_excluded(), false);
    /// assert_eq!(match_result.excluded_elements(), empty);
    ///
    /// // There is no answer at all:
    /// let match_result = subset_map.find(&[42]);
    ///
    /// assert_eq!(match_result.payload(), None);
    /// assert_eq!(match_result.is_not_found(), true);
    /// assert_eq!(match_result.is_found_and_perfect(), false);
    /// assert_eq!(match_result.is_found_and_excluded(), false);
    /// assert_eq!(match_result.excluded_elements(), empty);
    ///
    /// // A nearby match but that has a payload:
    /// let match_result = subset_map.find(&[3,1]);
    ///
    /// assert_eq!(match_result.is_found_and_perfect(), false);
    /// assert_eq!(match_result.is_found_and_excluded(), true);
    /// assert_eq!(match_result.is_found(), true);
    /// assert_eq!(match_result.payload(), Some(&vec![3]));
    /// assert_eq!(match_result.excluded_elements(), &[1]);
    /// ```
    pub fn find<'a>(&'a self, subset: &[E]) -> FindResult<'a, E, P>
    where
        E: Eq,
    {
        match self.lookup(subset) {
            LookupResult::Perfect(Some(p)) => FindResult::Perfect(p),
            LookupResult::Perfect(None) => FindResult::NotFound,
            LookupResult::Excluded(Some(p), e) => FindResult::Excluded(p, e),
            LookupResult::Excluded(None, _) => FindResult::NotFound,
            LookupResult::NoMatch => FindResult::NotFound,
        }
    }

    /// Sets the payload of all subsets to `None`
    /// where the given payload does not fulfill the `predicate`
    pub fn filter_values<F>(&mut self, mut predicate: F)
    where
        F: FnMut(&P) -> bool,
    {
        self.nodes
            .iter_mut()
            .for_each(|n| n.filter_values(&mut predicate))
    }

    /// Executes the given mutable closure `f`
    /// on the value of each node.
    pub fn walk_values<F>(&self, mut f: F)
    where
        F: FnMut(&P),
    {
        self.nodes.iter().for_each(|n| n.walk_values(&mut f))
    }

    /// Executes the given mutable closure `f`
    /// on the value of each node until the
    /// first closure returns false.
    pub fn walk_values_until<F>(&self, mut f: F)
    where
        F: FnMut(&P) -> bool,
    {
        for node in &self.nodes {
            if !node.walk_values_until(&mut f) {
                return;
            }
        }
    }

    /// Executes the given mutable closure `f`
    /// on the payload of each node
    pub fn walk_payloads<F>(&self, mut f: F)
    where
        F: FnMut(Option<&P>),
    {
        self.nodes.iter().for_each(|n| n.walk_payloads(&mut f))
    }

    /// Executes the given mutable closure `f`
    /// on the payload of each node until the
    /// first closure returns false.
    pub fn walk_payloads_until<F>(&self, mut f: F)
    where
        F: FnMut(Option<&P>) -> bool,
    {
        for node in &self.nodes {
            if !node.walk_payloads_until(&mut f) {
                return;
            }
        }
    }

    /// Walk all elements with their payloads
    pub fn walk<F>(&self, mut f: F)
    where
        F: FnMut(&[&E], Option<&P>),
    {
        self.nodes.iter().for_each(|n| n.walk(&mut f))
    }

    /// Executes the given mutable closure `f`
    /// on the payload of each node
    pub fn for_each_value<F>(&self, mut f: F)
    where
        F: FnMut(&P),
    {
        self.walk_values_until(|p| {
            f(p);
            true
        })
    }

    /// Executes the given mutable closure `f`
    /// on the payload of each node
    pub fn for_each_payload<F>(&self, mut f: F)
    where
        F: FnMut(Option<&P>),
    {
        self.walk_payloads_until(|p| {
            f(p);
            true
        })
    }

    /// Returns true if there are nodes and all
    /// of these have a payload set.
    pub fn all_subsets_have_values(&self) -> bool {
        if self.is_empty() {
            return false;
        }

        let mut all_set = true;

        self.walk_payloads_until(|p| {
            if p.is_none() {
                all_set = false;
                false
            } else {
                true
            }
        });

        all_set
    }

    /// Returns true if there are no subsets or all
    /// of these have no payload set.
    ///
    /// # Example
    ///
    /// An empty map has no values:
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::<u8, u8>::with_default(&[]);
    ///
    /// assert_eq!(subset_map.no_subset_with_value(), true);
    /// ```
    ///
    /// An map with a set entry has values:
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::<u8, u8>::with_default(&[1]);
    ///
    /// assert_eq!(subset_map.no_subset_with_value(), false);
    /// ```
    ///
    /// An non empty map where at least one subset has a value:
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let mut subset_map = SubsetMap::fill(&[1, 2], |c| c.len());
    ///
    /// subset_map.filter_values(|p| *p == 2);
    ///
    /// assert_eq!(subset_map.no_subset_with_value(), false);
    /// ```
    ///
    /// An non empty map where no subset has a value:
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let mut subset_map = SubsetMap::<u8, u8>::with_default(&[1, 2]);
    ///
    /// // Set all payloads to `None`
    /// subset_map.filter_values(|p| false);
    ///
    /// assert_eq!(subset_map.no_subset_with_value(), true);
    /// ```
    pub fn no_subset_with_value(&self) -> bool {
        if self.is_empty() {
            return true;
        }

        let mut no_value_set = true;

        self.walk_payloads_until(|p| {
            if p.is_some() {
                no_value_set = false;
                false
            } else {
                true
            }
        });

        no_value_set
    }

    /// Returns true if the map is empty and contains no subsets.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// The number of subsets in this map
    pub fn size(&self) -> usize {
        2usize.pow(self.nodes.len() as u32) - 1
    }
}

impl<E, P> Default for SubsetMap<E, P> {
    fn default() -> Self {
        SubsetMap {
            nodes: Default::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
struct SubsetMapNode<E, P> {
    pub element: E,
    pub payload: Option<P>,
    pub nodes: Nodes<E, P>,
}

impl<E, P> SubsetMapNode<E, P> {
    pub fn filter_values<F>(&mut self, predicate: &mut F)
    where
        F: FnMut(&P) -> bool,
    {
        let keep = self.payload.as_ref().map(|p| predicate(p)).unwrap_or(true);
        if !keep {
            self.payload = None;
        }
        self.nodes
            .iter_mut()
            .for_each(|n| n.filter_values(predicate))
    }

    pub fn walk_values<F>(&self, f: &mut F)
    where
        F: FnMut(&P),
    {
        if let Some(ref payload) = self.payload {
            f(payload);
        }
        self.nodes.iter().for_each(|n| n.walk_values(f))
    }

    pub fn walk_payloads<F>(&self, f: &mut F)
    where
        F: FnMut(Option<&P>),
    {
        f(self.payload.as_ref());
        self.nodes.iter().for_each(|n| n.walk_payloads(f))
    }

    pub fn walk_values_until<F>(&self, f: &mut F) -> bool
    where
        F: FnMut(&P) -> bool,
    {
        let go_on = if let Some(ref payload) = self.payload {
            f(payload)
        } else {
            true
        };

        if go_on {
            for node in &self.nodes {
                if !node.walk_values_until(f) {
                    return false;
                }
            }
        }

        true
    }

    pub fn walk_payloads_until<F>(&self, f: &mut F) -> bool
    where
        F: FnMut(Option<&P>) -> bool,
    {
        if f(self.payload.as_ref()) {
            for node in &self.nodes {
                if !node.walk_payloads_until(f) {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }

    pub fn walk<F>(&self, mut f: F)
    where
        F: FnMut(&[&E], Option<&P>),
    {
        let mut elements = Vec::new();
        self.walk_internal(&mut elements, &mut f)
    }

    fn walk_internal<'a, F>(&'a self, elements: &mut Vec<&'a E>, f: &mut F)
    where
        F: FnMut(&[&E], Option<&P>),
    {
        elements.push(&self.element);
        f(elements.as_slice(), self.payload.as_ref());
        self.nodes.iter().for_each(|n| n.walk_internal(elements, f));
        elements.pop();
    }
}

/// The result of `SubsetMap::lookup`.
///
/// It can either be a perfect match on the subset
/// or a match where some elements of the input set
/// had to be excluded.
///
/// A value of `None` for the payload indicates
/// that there was a match for a given subset but
/// nevertheless there was no payload stored for
/// that subset.
#[derive(Debug)]
pub enum LookupResult<'a, E, P: 'a> {
    /// The input set exactly matched a combination
    /// of the original set.
    Perfect(Option<&'a P>),
    /// There were some elements in the input set that had
    /// to be excluded to match a subset of the original set
    ///
    /// The excluded elements are returned.
    Excluded(Option<&'a P>, Vec<E>),
    /// There was no match at all for the given subset
    NoMatch,
}

impl<'a, E, P> LookupResult<'a, E, P> {
    pub fn payload(&self) -> Option<&P> {
        match *self {
            LookupResult::Perfect(p) => p,
            LookupResult::Excluded(p, _) => p,
            LookupResult::NoMatch => None,
        }
    }

    /// Returns the excluded elements if there was
    /// a match at all.
    ///
    /// If there was no match the returned slice
    /// is also empty.
    pub fn excluded_elements(&self) -> &[E] {
        match *self {
            LookupResult::Perfect(_) => &[],
            LookupResult::Excluded(_, ref skipped) => &*skipped,
            LookupResult::NoMatch => &[],
        }
    }

    /// Returns `true` if there was a perfect match
    pub fn is_perfect(&self) -> bool {
        match *self {
            LookupResult::Perfect(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if there was a match
    /// but some elements had to be excluded
    pub fn is_excluded(&self) -> bool {
        match *self {
            LookupResult::Excluded(_, _) => true,
            _ => false,
        }
    }

    /// Returns `true` if there was no match at all
    pub fn is_no_match(&self) -> bool {
        !self.is_match()
    }

    /// Returns `true` if there was a match even
    /// though some elements had to be excluded
    pub fn is_match(&self) -> bool {
        match *self {
            LookupResult::NoMatch => false,
            _ => true,
        }
    }
}

/// The result of `SubsetMap::find`.
///
/// It can either be a perfect match on the subset
/// or a match where some elements of the input set
/// had to be excluded.
///
/// For `FindResult::NotFound` no tracking of
/// excluded elements is done.
#[derive(Debug)]
pub enum FindResult<'a, E, P: 'a> {
    /// The input set exactly matched a combination
    /// of the original set and there was a payload.
    Perfect(&'a P),
    /// There were some elements in the input set that had
    /// to be excluded to match a subset of the original set.
    ///
    /// Still there was a payload at the given position.
    ///
    /// The excluded elements are returned.
    Excluded(&'a P, Vec<E>),
    /// There was no match at all or the payload
    /// for the matched subset was `None`
    NotFound,
}

impl<'a, E, P> FindResult<'a, E, P> {
    pub fn payload(&self) -> Option<&P> {
        match *self {
            FindResult::Perfect(p) => Some(p),
            FindResult::Excluded(p, _) => Some(p),
            FindResult::NotFound => None,
        }
    }

    /// Returns the excluded elements if there was
    /// a match at all.
    ///
    /// If there was no match the returned slice
    /// is also empty.
    pub fn excluded_elements(&self) -> &[E] {
        match *self {
            FindResult::Perfect(_) => &[],
            FindResult::Excluded(_, ref skipped) => &*skipped,
            FindResult::NotFound => &[],
        }
    }

    /// Returns `true` if there was a perfect match
    pub fn is_found_and_perfect(&self) -> bool {
        match *self {
            FindResult::Perfect(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if there was a match
    /// but some elements had to be excluded
    pub fn is_found_and_excluded(&self) -> bool {
        match *self {
            FindResult::Excluded(_, _) => true,
            _ => false,
        }
    }

    /// Returns `true` if there was no match
    /// or if the payload for the matched subset was
    /// `None`
    pub fn is_not_found(&self) -> bool {
        !self.is_found()
    }

    /// Returns `true` if there was a match even
    /// though some elements had to be excluded
    /// and if there was a payload for the matched
    /// subset.
    pub fn is_found(&self) -> bool {
        match *self {
            FindResult::NotFound => false,
            _ => true,
        }
    }
}

fn init_root<E, P, F, X>(elements: &[E], init_with: &mut F) -> Result<SubsetMap<E, P>, X>
where
    E: Clone,
    F: FnMut(&[E]) -> Result<Option<P>, X>,
{
    let mut stack = Vec::new();
    let mut nodes = Vec::new();

    for fixed in 0..elements.len() {
        let element = elements[fixed].clone();
        let payload = init_with(&elements[fixed..=fixed])?;
        let mut node = SubsetMapNode {
            element,
            payload,
            nodes: Vec::new(),
        };
        stack.clear();
        stack.push(elements[fixed].clone());
        init_node(elements, &mut stack, fixed, &mut node, init_with)?;
        nodes.push(node)
    }
    Ok(SubsetMap { nodes })
}

fn init_node<E, P, F, X>(
    elements: &[E],
    stack: &mut Vec<E>,
    fixed: usize,
    into: &mut SubsetMapNode<E, P>,
    init_with: &mut F,
) -> Result<(), X>
where
    E: Clone,
    F: FnMut(&[E]) -> Result<Option<P>, X>,
{
    for fixed in fixed + 1..elements.len() {
        stack.push(elements[fixed].clone());
        let mut node = SubsetMapNode {
            element: elements[fixed].clone(),
            payload: init_with(&stack)?,
            nodes: Vec::new(),
        };
        let _ = init_node(elements, stack, fixed, &mut node, init_with);
        stack.pop();
        into.nodes.push(node);
    }
    Ok(())
}

fn get<'a, 'b, E, P>(subset: &'b [E], nodes: &'a [SubsetMapNode<E, P>]) -> Option<&'a P>
where
    E: Eq,
{
    let mut nodes = nodes;
    let mut result = None;
    for element in subset {
        if let Some(node) = nodes.iter().find(|n| n.element == *element) {
            result = node.payload.as_ref();
            nodes = &node.nodes;
        } else {
            return None;
        }
    }

    result
}

fn lookup<'a, 'b, E, P>(subset: &'b [E], nodes: &'a [SubsetMapNode<E, P>]) -> LookupResult<'a, E, P>
where
    E: Eq + Clone,
{
    let mut excluded = Vec::new();
    let mut nodes = nodes;
    let mut result_node = None;

    for element in subset {
        if let Some(node) = nodes.iter().find(|n| n.element == *element) {
            result_node = Some(node);
            nodes = &node.nodes;
        } else {
            excluded.push(element.clone())
        }
    }

    if let Some(result_node) = result_node {
        if excluded.is_empty() {
            LookupResult::Perfect(result_node.payload.as_ref())
        } else {
            LookupResult::Excluded(result_node.payload.as_ref(), excluded)
        }
    } else {
        LookupResult::NoMatch
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn create_empty() {
        let sample = SubsetMap::<u32, ()>::default();

        assert!(sample.is_empty());
    }

    #[test]
    fn one_element() {
        let sample = SubsetMap::fill(&[1], |_| 1);

        assert_eq!(sample.get(&[1]), Some(&1));
        assert_eq!(sample.get(&[]), None);
        assert_eq!(sample.get(&[2]), None);
    }

    #[test]
    fn two_elements() {
        let sample = SubsetMap::fill(&[1, 2], |x| x.iter().sum::<i32>());

        assert_eq!(sample.get(&[1]), Some(&1));
        assert_eq!(sample.get(&[2]), Some(&2));
        assert_eq!(sample.get(&[1, 2]), Some(&3));
        assert_eq!(sample.get(&[]), None);
        assert_eq!(sample.get(&[2, 1]), None);
        assert_eq!(sample.get(&[0]), None);
        assert_eq!(sample.get(&[0, 1]), None);
    }

    #[test]
    fn three_elements() {
        let sample = SubsetMap::fill(&[1, 2, 3], |x| x.iter().sum::<i32>());

        assert_eq!(sample.get(&[1]), Some(&1));
        assert_eq!(sample.get(&[2]), Some(&2));
        assert_eq!(sample.get(&[3]), Some(&3));
        assert_eq!(sample.get(&[1, 2]), Some(&3));
        assert_eq!(sample.get(&[2, 3]), Some(&5));
        assert_eq!(sample.get(&[1, 3]), Some(&4));
        assert_eq!(sample.get(&[1, 2, 3]), Some(&6));
        assert_eq!(sample.get(&[]), None);
        assert_eq!(sample.get(&[2, 1]), None);
        assert_eq!(sample.get(&[0]), None);
        assert_eq!(sample.get(&[0, 1]), None);
    }

    #[test]
    fn three_elements_identity_vec() {
        let sample = SubsetMap::fill(&[1, 2, 3], |x| x.to_vec());

        assert_eq!(sample.get(&[1]), Some(&vec![1]));
        assert_eq!(sample.get(&[2]), Some(&vec![2]));
        assert_eq!(sample.get(&[3]), Some(&vec![3]));
        assert_eq!(sample.get(&[1, 2]), Some(&vec![1, 2]));
        assert_eq!(sample.get(&[2, 3]), Some(&vec![2, 3]));
        assert_eq!(sample.get(&[1, 3]), Some(&vec![1, 3]));
        assert_eq!(sample.get(&[1, 2, 3]), Some(&vec![1, 2, 3]));
    }

    #[test]
    fn walk_5_elems_keeps_order() {
        let elements: Vec<_> = (0..5).collect();

        let mut n = 0;
        let map = SubsetMap::fill(&elements, |_x| {
            n += 1;
            n
        });

        let mut n = 0;
        map.walk(|_elements, payload| {
            n += 1;
            assert_eq!(payload, Some(&n));
        })
    }

    #[test]
    fn test_lookup_result() {
        let subset_map = SubsetMap::new(&[1u32, 2, 3, 4], |x| {
            if x == &[2, 3] {
                None
            } else {
                let payload = x.iter().cloned().collect::<Vec<_>>();
                Some(payload)
            }
        });

        let empty: &[u32] = &[];

        let match_result = subset_map.lookup(&[]);
        assert_eq!(match_result.payload(), None);
        assert_eq!(match_result.excluded_elements(), empty);
        assert_eq!(match_result.is_match(), false);
        assert_eq!(match_result.is_perfect(), false);
        assert_eq!(match_result.is_excluded(), false);

        let match_result = subset_map.lookup(&[1]);
        assert_eq!(match_result.payload(), Some(&vec![1]));
        assert_eq!(match_result.excluded_elements(), empty);
        assert_eq!(match_result.is_match(), true);
        assert_eq!(match_result.is_perfect(), true);
        assert_eq!(match_result.is_excluded(), false);

        let match_result = subset_map.lookup(&[2, 3]);
        assert_eq!(match_result.payload(), None);
        assert_eq!(match_result.excluded_elements(), empty);
        assert_eq!(match_result.is_match(), true);
        assert_eq!(match_result.is_perfect(), true);
        assert_eq!(match_result.is_excluded(), false);

        let match_result = subset_map.lookup(&[42]);
        assert_eq!(match_result.is_no_match(), true);
        assert_eq!(match_result.is_perfect(), false);
        assert_eq!(match_result.is_excluded(), false);
        assert_eq!(match_result.excluded_elements(), empty);

        let match_result = subset_map.lookup(&[42, 3]);
        assert_eq!(match_result.payload(), Some(&vec![3]));
        assert_eq!(match_result.excluded_elements(), &[42]);
        assert_eq!(match_result.is_perfect(), false);
        assert_eq!(match_result.is_excluded(), true);
        assert_eq!(match_result.is_match(), true);

        let match_result = subset_map.lookup(&[3, 1]);
        assert_eq!(match_result.payload(), Some(&vec![3]));
        assert_eq!(match_result.excluded_elements(), &[1]);
        assert_eq!(match_result.is_perfect(), false);
        assert_eq!(match_result.is_excluded(), true);
        assert_eq!(match_result.is_match(), true);

        let match_result = subset_map.lookup(&[3, 1, 4, 2]);
        assert_eq!(match_result.payload(), Some(&vec![3, 4]));
        assert_eq!(match_result.excluded_elements(), &[1, 2]);
        assert_eq!(match_result.is_perfect(), false);
        assert_eq!(match_result.is_excluded(), true);
        assert_eq!(match_result.is_match(), true);

        let match_result = subset_map.lookup(&[4, 3, 2, 1]);
        assert_eq!(match_result.payload(), Some(&vec![4]));
        assert_eq!(match_result.excluded_elements(), &[3, 2, 1]);
        assert_eq!(match_result.is_perfect(), false);
        assert_eq!(match_result.is_excluded(), true);
        assert_eq!(match_result.is_match(), true);

        let match_result = subset_map.lookup(&[99, 2, 1, 77, 78, 3, 4, 2, 1, 2]);
        assert_eq!(match_result.payload(), Some(&vec![2, 3, 4]));
        assert_eq!(match_result.excluded_elements(), &[99, 1, 77, 78, 2, 1, 2]);
        assert_eq!(match_result.is_perfect(), false);
        assert_eq!(match_result.is_excluded(), true);
        assert_eq!(match_result.is_match(), true);
    }
}
