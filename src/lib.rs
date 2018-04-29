type Nodes<I, P> = Vec<SubsetMapNode<I, P>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubsetMap<E, P> {
    nodes: Nodes<E, P>,
}

impl<E, P> SubsetMap<E, P>
where
    E: Clone,
{
    pub fn new<F>(elements: &[E], mut init: F) -> SubsetMap<E, P>
    where
        F: FnMut(&[E]) -> P,
    {
        init_root(elements, &mut init)
    }

    pub fn with_value<F>(elements: &[E], mut init: F) -> SubsetMap<E, P>
    where
        F: FnMut() -> P,
    {
        init_root(elements, &mut |_| init())
    }

    pub fn with_defaults(elements: &[E]) -> SubsetMap<E, P>
    where
        P: Default,
    {
        init_root(elements, &mut |_| P::default())
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn lookup<'a>(&'a self, subset: &'a [E]) -> Option<&'a P>
    where
        E: Eq,
    {
        match self.find(subset) {
            Some(MatchQuality::Perfect(p)) => Some(p),
            _ => None,
        }
    }

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
struct SubsetMapNode<E, P> {
    pub element: E,
    pub payload: P,
    pub nodes: Nodes<E, P>,
}

pub enum MatchQuality<'a, 'b, E: 'a, P: 'b> {
    Perfect(&'b P),
    Nearby(&'b P, Vec<&'a E>),
}

impl<'a, 'b, E, P> MatchQuality<'a, 'b, E, P> {
    pub fn value(&self) -> &P {
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
) -> Option<&'a P>
where
    E: Eq,
{
    if subset.is_empty() {
        Some(&node.payload)
    } else {
        find_in_next_node(subset, &node.nodes, skipped)
    }
}

fn find_in_next_node<'a, 'b, E, P>(
    subset: &'b [E],
    nodes: &'a [SubsetMapNode<E, P>],
    skipped: &mut Vec<&'b E>,
) -> Option<&'a P>
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

fn init_root<E, P, F>(elements: &[E], init_with: &mut F) -> SubsetMap<E, P>
where
    E: Clone,
    F: FnMut(&[E]) -> P,
{
    let mut stack = Vec::new();
    let nodes: Nodes<_, _> = (0..elements.len())
        .map(|fixed| {
            let element = elements[fixed].clone();
            let payload = init_with(&elements[fixed..fixed + 1]);
            let mut node = SubsetMapNode {
                element,
                payload,
                nodes: Vec::new(),
            };
            stack.clear();
            stack.push(elements[fixed].clone());
            init_node(elements, &mut stack, fixed, &mut node, init_with);
            node
        })
        .collect();
    SubsetMap { nodes }
}

fn init_node<E, P, F>(
    elements: &[E],
    stack: &mut Vec<E>,
    fixed: usize,
    into: &mut SubsetMapNode<E, P>,
    init_with: &mut F,
) where
    E: Clone,
    F: FnMut(&[E]) -> P,
{
    for fixed in fixed + 1..elements.len() {
        stack.push(elements[fixed].clone());
        let mut node = SubsetMapNode {
            element: elements[fixed].clone(),
            payload: init_with(&stack),
            nodes: Vec::new(),
        };
        init_node(elements, stack, fixed, &mut node, init_with);
        stack.pop();
        into.nodes.push(node);
    }
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
        let sample = SubsetMap::new(&[1], |_| 1);

        assert_eq!(sample.lookup(&[1]), Some(&1));
        assert_eq!(sample.lookup(&[]), None);
        assert_eq!(sample.lookup(&[2]), None);
    }

    #[test]
    fn two_elements() {
        let sample = SubsetMap::new(&[1, 2], |x| x.iter().sum::<i32>());

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
        let sample = SubsetMap::new(&[1, 2, 3], |x| x.iter().sum::<i32>());

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
        let sample = SubsetMap::new(&[1, 2, 3], |x| x.iter().cloned().collect::<Vec<_>>());

        assert_eq!(sample.lookup(&[1]), Some(&vec![1]));
        assert_eq!(sample.lookup(&[2]), Some(&vec![2]));
        assert_eq!(sample.lookup(&[3]), Some(&vec![3]));
        assert_eq!(sample.lookup(&[1, 2]), Some(&vec![1, 2]));
        assert_eq!(sample.lookup(&[2, 3]), Some(&vec![2, 3]));
        assert_eq!(sample.lookup(&[1, 3]), Some(&vec![1, 3]));
        assert_eq!(sample.lookup(&[1, 2, 3]), Some(&vec![1, 2, 3]));
    }

}
