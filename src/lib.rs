type Nodes<I, P> = Vec<SubsetMapNode<I, P>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubsetMap<I, P> {
    nodes: Nodes<I, P>,
}

impl<I, P> SubsetMap<I, P>
where
    I: Clone,
{
    pub fn new<F>(ids: &[I], init: F) -> SubsetMap<I, P>
    where
        F: Fn(&[I]) -> P,
    {
        init_root(ids, &init)
    }

    pub fn with_value<F>(ids: &[I], init: F) -> SubsetMap<I, P>
    where
        F: Fn() -> P,
    {
        init_root(ids, &|_| init())
    }

    pub fn with_defaults(ids: &[I]) -> SubsetMap<I, P>
    where
        P: Default,
    {
        init_root(ids, &|_| P::default())
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn lookup<'a>(&'a self, subset: &'a [I]) -> Option<&'a P>
    where
        I: Eq,
    {
        match self.find(subset) {
            Some(MatchQuality::Perfect(p)) => Some(p),
            _ => None,
        }
    }

    pub fn find<'a>(&'a self, subset: &'a [I]) -> Option<MatchQuality<'a, 'a, I, P>>
    where
        I: Eq,
    {
        if subset.is_empty() {
            None
        } else {
            let mut skipped = Vec::with_capacity(subset.len());
            if let Some(found) = find_next_node(subset, &self.nodes, &mut skipped)
                .and_then(|next_node| find(subset, next_node, &mut skipped))
            {
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
struct SubsetMapNode<I, P> {
    pub id: I,
    pub payload: P,
    pub nodes: Nodes<I, P>,
}

pub enum MatchQuality<'a, 'b, I: 'a, P: 'b> {
    Perfect(&'b P),
    Nearby(&'b P, Vec<&'a I>),
}

impl<'a, 'b, I, P> MatchQuality<'a, 'b, I, P> {
    pub fn value(&self) -> &P {
        match *self {
            MatchQuality::Perfect(p) => p,
            MatchQuality::Nearby(p, _) => p,
        }
    }
}

fn find<'a, 'b, I, P>(
    subset: &'b [I],
    node: &'a SubsetMapNode<I, P>,
    skipped: &mut Vec<&'b I>,
) -> Option<&'a P>
where
    I: Eq,
    P: ,
{
    if subset.is_empty() {
        Some(&node.payload)
    } else {
        find_next_node(subset, &node.nodes, skipped)
            .and_then(|next_node| find(subset, next_node, skipped))
    }
}

fn find_next_node<'a, 'b, I, P>(
    subset: &'b [I],
    nodes: &'a [SubsetMapNode<I, P>],
    skipped: &mut Vec<&'b I>,
) -> Option<&'a SubsetMapNode<I, P>> {
    unimplemented!()
}

fn init_root<I, P, F>(ids: &[I], init_with: &F) -> SubsetMap<I, P>
where
    I: Clone,
    F: Fn(&[I]) -> P,
{
    let nodes: Nodes<_, _> = (0..ids.len())
        .map(|fixed| {
            let id = ids[fixed].clone();
            let payload = init_with(&ids[fixed..fixed + 1]);
            let mut node = SubsetMapNode {
                id,
                payload,
                nodes: Vec::new(),
            };
            init_node(ids, fixed, fixed, &mut node, init_with);
            node
        })
        .collect();
    SubsetMap { nodes }
}

fn init_node<I, P, F>(
    ids: &[I],
    initial: usize,
    fixed: usize,
    into: &mut SubsetMapNode<I, P>,
    init_with: &F,
) where
    I: Clone,
    F: Fn(&[I]) -> P,
{
    for fixed in fixed + 1..ids.len() {
        let mut node = SubsetMapNode {
            id: ids[fixed].clone(),
            payload: init_with(&ids[initial..fixed]),
            nodes: Vec::new(),
        };
        init_node(ids, initial, fixed, &mut node, init_with);
        into.nodes.push(node);
    }
}

impl<I, P> Default for SubsetMap<I, P> {
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
    fn bogus() {
        let sample = SubsetMap::<_, ()>::with_defaults(&[]);
        let expected = SubsetMap::with_defaults(&[1, 2, 3]);

        assert_eq!(sample, expected);
    }
}
