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
//! assert_eq!(subset_map.lookup(&[1]), Some(&vec![1]));
//! assert_eq!(subset_map.lookup(&[2]), Some(&vec![2]));
//! assert_eq!(subset_map.lookup(&[3]), Some(&vec![3]));
//! assert_eq!(subset_map.lookup(&[1, 2]), Some(&vec![1, 2]));
//! assert_eq!(subset_map.lookup(&[2, 3]), Some(&vec![2, 3]));
//! assert_eq!(subset_map.lookup(&[1, 3]), Some(&vec![1, 3]));
//! assert_eq!(subset_map.lookup(&[1, 2, 3]), Some(&vec![1, 2, 3]));
//!
//! // No internal ordering is performed:
//! // The position in the original set is crucial:
//! assert_eq!(subset_map.lookup(&[2,1]), None);
//! ```
//!
//! ## Features
//!
//! The `serde` feature allows serialization and deserialization with `serde`.
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
    /// # Example
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::fill(&[1, 2], |x| x.iter().sum::<i32>());
    /// assert_eq!(subset_map.lookup(&[1]), Some(&1));
    /// assert_eq!(subset_map.lookup(&[2]), Some(&2));
    /// assert_eq!(subset_map.lookup(&[1, 2]), Some(&3));
    /// assert_eq!(subset_map.lookup(&[]), None);
    /// assert_eq!(subset_map.lookup(&[2, 1]), None);
    /// assert_eq!(subset_map.lookup(&[0]), None);
    /// assert_eq!(subset_map.lookup(&[0, 1]), None);
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
    /// # Example
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::fill(&[1, 2], |x| x.iter().sum::<i32>());
    /// assert_eq!(subset_map.lookup(&[1]), Some(&1));
    /// assert_eq!(subset_map.lookup(&[2]), Some(&2));
    /// assert_eq!(subset_map.lookup(&[1, 2]), Some(&3));
    /// assert_eq!(subset_map.lookup(&[]), None);
    /// assert_eq!(subset_map.lookup(&[2, 1]), None);
    /// assert_eq!(subset_map.lookup(&[0]), None);
    /// assert_eq!(subset_map.lookup(&[0, 1]), None);
    /// ```
    pub fn fill<F>(elements: &[E], mut init: F) -> SubsetMap<E, P>
    where
        F: FnMut(&[E]) -> P,
    {
        init_root::<_, _, _, ()>(elements, &mut |elements| Ok(Some(init(elements)))).unwrap()
    }

    pub fn init<F, X>(elements: &[E], mut init: F) -> Result<SubsetMap<E, P>, X>
    where
        F: FnMut(&[E]) -> Result<Option<P>, X>,
    {
        init_root(elements, &mut init)
    }

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
    /// assert_eq!(subset_map.lookup(&[1]), Some(&42));
    /// assert_eq!(subset_map.lookup(&[2]), Some(&42));
    /// assert_eq!(subset_map.lookup(&[1, 2]), Some(&42));
    /// assert_eq!(subset_map.lookup(&[]), None);
    /// assert_eq!(subset_map.lookup(&[2, 1]), None);
    /// assert_eq!(subset_map.lookup(&[0]), None);
    /// assert_eq!(subset_map.lookup(&[0, 1]), None);
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
    /// assert_eq!(subset_map.lookup(&[1]), Some(&0));
    /// assert_eq!(subset_map.lookup(&[2]), Some(&0));
    /// assert_eq!(subset_map.lookup(&[1, 2]), Some(&0));
    /// assert_eq!(subset_map.lookup(&[]), None);
    /// assert_eq!(subset_map.lookup(&[2, 1]), None);
    /// assert_eq!(subset_map.lookup(&[0]), None);
    /// assert_eq!(subset_map.lookup(&[0, 1]), None);
    /// ```
    pub fn with_default(elements: &[E]) -> SubsetMap<E, P>
    where
        P: Default,
    {
        init_root::<_, _, _, ()>(elements, &mut |_| Ok(Some(P::default()))).unwrap()
    }

    /// Returns true if the map is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Looks up a payload by the given subset.
    ///
    /// Only "perfect" matches on `subset` are returned.
    ///
    /// ```
    /// use subset_map::*;
    ///
    /// let subset_map = SubsetMap::fill(&[1, 2, 3], |x| x.iter().cloned().collect::<Vec<_>>());
    /// assert_eq!(subset_map.lookup(&[1]), Some(&vec![1]));
    /// assert_eq!(subset_map.lookup(&[2]), Some(&vec![2]));
    /// assert_eq!(subset_map.lookup(&[3]), Some(&vec![3]));
    /// assert_eq!(subset_map.lookup(&[1, 2]), Some(&vec![1, 2]));
    /// assert_eq!(subset_map.lookup(&[2, 3]), Some(&vec![2, 3]));
    /// assert_eq!(subset_map.lookup(&[1, 3]), Some(&vec![1, 3]));
    /// assert_eq!(subset_map.lookup(&[1, 2, 3]), Some(&vec![1, 2, 3]));
    ///
    /// assert_eq!(subset_map.lookup(&[]), None);
    /// assert_eq!(subset_map.lookup(&[7]), None);
    /// assert_eq!(subset_map.lookup(&[3, 2, 1]), None);
    /// assert_eq!(subset_map.lookup(&[1, 3, 2]), None);
    /// assert_eq!(subset_map.lookup(&[3, 2, 1]), None);
    /// assert_eq!(subset_map.lookup(&[2, 1]), None);
    /// ```
    pub fn lookup<'a>(&'a self, subset: &'a [E]) -> Option<&'a P>
    where
        E: Eq,
    {
        match self.find(subset) {
            Some(MatchQuality::Perfect(p)) => p,
            _ => None,
        }
    }

    /// Looks up a payload by the given subset and returns a clone.
    ///
    /// Only perfect matches on `subset` are returned. See `lookup`.
    pub fn lookup_owned(&self, subset: &[E]) -> Option<P>
    where
        E: Eq,
        P: Clone,
    {
        match self.find(subset) {
            Some(MatchQuality::Perfect(p)) => p.cloned(),
            _ => None,
        }
    }

    /// Finds a payload by the given subset.
    ///
    /// Elements in `subset` that are not part of the initial set are
    /// skipped.
    ///
    /// If no element of the input set matched `None` is returned.
    pub fn find<'a>(&'a self, subset: &'a [E]) -> Option<MatchQuality<'a, 'a, E, P>>
    where
        E: Eq,
    {
        if subset.is_empty() {
            None
        } else {
            let mut skipped = Vec::with_capacity(subset.len());
            if let Some(found) = find_in_next_node(subset, &self.nodes, &mut skipped) {
                if skipped.is_empty() {
                    Some(MatchQuality::Perfect(found))
                } else {
                    Some(MatchQuality::Nearby(found, skipped))
                }
            } else {
                None
            }
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

/// The result of `SubsetMap::find`.
///
/// It can either be a perfect match on the subset
/// or a match where some elements of the input set
/// had to be skipped.
pub enum MatchQuality<'a, 'b, E: 'a, P: 'b> {
    /// The input set exactly matched a combination
    /// of the original set.
    Perfect(Option<&'b P>),
    /// There were some elements in the input set that had
    /// to be skipped to match a subset of the original set.alloc
    ///
    /// The skipped elements are returned.
    Nearby(Option<&'b P>, Vec<&'a E>),
}

impl<'a, 'b, E, P> MatchQuality<'a, 'b, E, P> {
    pub fn value(&self) -> Option<&P> {
        match *self {
            MatchQuality::Perfect(p) => p,
            MatchQuality::Nearby(p, _) => p,
        }
    }
}

fn find<'a, 'b, E, P>(
    subset: &'b [E],
    node: &'a SubsetMapNode<E, P>,
    skipped: &mut Vec<&'b E>,
) -> Option<Option<&'a P>>
where
    E: Eq,
{
    if subset.is_empty() {
        Some(node.payload.as_ref())
    } else {
        find_in_next_node(subset, &node.nodes, skipped)
    }
}

fn find_in_next_node<'a, 'b, E, P>(
    subset: &'b [E],
    nodes: &'a [SubsetMapNode<E, P>],
    skipped: &mut Vec<&'b E>,
) -> Option<Option<&'a P>>
where
    E: Eq,
{
    let mut idx = 1;
    for element in subset {
        if let Some(node) = nodes.iter().find(|n| n.element == *element) {
            return find(&subset[idx..], node, skipped);
        }
        idx += 1;
        skipped.push(element);
    }

    None
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
        let payload = init_with(&elements[fixed..fixed + 1])?;
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

impl<E, P> Default for SubsetMap<E, P> {
    fn default() -> Self {
        SubsetMap {
            nodes: Default::default(),
        }
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

        assert_eq!(sample.lookup(&[1]), Some(&1));
        assert_eq!(sample.lookup(&[]), None);
        assert_eq!(sample.lookup(&[2]), None);
    }

    #[test]
    fn two_elements() {
        let sample = SubsetMap::fill(&[1, 2], |x| x.iter().sum::<i32>());

        assert_eq!(sample.lookup(&[1]), Some(&1));
        assert_eq!(sample.lookup(&[2]), Some(&2));
        assert_eq!(sample.lookup(&[1, 2]), Some(&3));
        assert_eq!(sample.lookup(&[]), None);
        assert_eq!(sample.lookup(&[2, 1]), None);
        assert_eq!(sample.lookup(&[0]), None);
        assert_eq!(sample.lookup(&[0, 1]), None);
    }

    #[test]
    fn three_elements() {
        let sample = SubsetMap::fill(&[1, 2, 3], |x| x.iter().sum::<i32>());

        assert_eq!(sample.lookup(&[1]), Some(&1));
        assert_eq!(sample.lookup(&[2]), Some(&2));
        assert_eq!(sample.lookup(&[3]), Some(&3));
        assert_eq!(sample.lookup(&[1, 2]), Some(&3));
        assert_eq!(sample.lookup(&[2, 3]), Some(&5));
        assert_eq!(sample.lookup(&[1, 3]), Some(&4));
        assert_eq!(sample.lookup(&[1, 2, 3]), Some(&6));
        assert_eq!(sample.lookup(&[]), None);
        assert_eq!(sample.lookup(&[2, 1]), None);
        assert_eq!(sample.lookup(&[0]), None);
        assert_eq!(sample.lookup(&[0, 1]), None);
    }

    #[test]
    fn three_elements_identity_vec() {
        let sample = SubsetMap::fill(&[1, 2, 3], |x| x.iter().cloned().collect::<Vec<_>>());

        assert_eq!(sample.lookup(&[1]), Some(&vec![1]));
        assert_eq!(sample.lookup(&[2]), Some(&vec![2]));
        assert_eq!(sample.lookup(&[3]), Some(&vec![3]));
        assert_eq!(sample.lookup(&[1, 2]), Some(&vec![1, 2]));
        assert_eq!(sample.lookup(&[2, 3]), Some(&vec![2, 3]));
        assert_eq!(sample.lookup(&[1, 3]), Some(&vec![1, 3]));
        assert_eq!(sample.lookup(&[1, 2, 3]), Some(&vec![1, 2, 3]));
    }
}
