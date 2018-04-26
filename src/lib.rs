pub type Nodes<I, P> = Vec<Node<I, P>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Root<I, P> {
    pub nodes: Nodes<I, P>,
}

impl<I, P> Root<I, P>
where
    I: Clone,
    P: Default,
{
    pub fn new(ids: &[I]) -> Root<I, P> {
        init_root(ids, &|| P::default())
    }
}

impl<I, P> Root<I, P>
where
    I: Clone,
{
    pub fn init_with<F>(ids: &[I], init: F) -> Root<I, P>
    where
        F: Fn() -> P,
    {
        init_root(ids, &init)
    }
}

impl<I, P> Root<I, P> {
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn combinations(&self) -> Vec<Vec<&I>> {
        unimplemented!()
    }

    pub fn iter(&self) -> Iter<I, P> {
        unimplemented!()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node<I, P> {
    pub id: I,
    pub payload: P,
    pub nodes: Nodes<I, P>,
}

pub trait NodeLike {
    type I;
    type P;
    fn nodes(&self) -> &[Node<Self::I, Self::P>];
}

impl<I, P> NodeLike for Root<I, P> {
    type I = I;
    type P = P;
    fn nodes(&self) -> &[Node<Self::I, Self::P>] {
        &self.nodes
    }
}

impl<I, P> NodeLike for Node<I, P> {
    type I = I;
    type P = P;
    fn nodes(&self) -> &[Node<Self::I, Self::P>] {
        &self.nodes
    }
}

pub struct Iter<'a, I, P>
where
    I: 'a,
    P: 'a,
{
    root: &'a Root<I, P>,
    root_index: usize,
    stack: Vec<(usize, &'a Node<I, P>)>,
    ids: Vec<I>,
}

impl<'a, I, P> Iter<'a, I, P> {
    pub fn new(root: &'a Root<I, P>) -> Self {
        Iter {
            root,
            root_index: 0,
            stack: Vec::with_capacity(root.nodes.len()),
            ids: Vec::with_capacity(root.nodes.len()),
        }
    }
}

impl<'a, I, P> Iterator for Iter<'a, I, P>
where
    I: 'a,
    P: 'a,
{
    type Item = (&'a [I], &'a P);

    fn next(&mut self) -> Option<Self::Item> {
        if self.root_index < self.root.nodes.len() {
            if self.stack.is_empty() {
                self.stack.push((0, &self.root.nodes[self.root_index]));
            }
            let &mut (current_index, current_node) = self.stack.last_mut().unwrap();
            let result = if current_index < current_node.nodes.len() {
                self.ids.push(current_node.id);
                Some((&*self.ids, &current_node.payload))
            } else {
                self.stack.pop();
                if self.stack.is_empty() {
                    self.root_index += 1;
                }
                None
            };
            result
        } else {
            None
        }
    }
}

fn init_root<I, P, F>(ids: &[I], init_with: &F) -> Root<I, P>
where
    I: Clone,
    F: Fn() -> P,
{
    let nodes: Nodes<_, _> = (0..ids.len())
        .map(|fixed| {
            let mut node = Node {
                id: ids[fixed].clone(),
                payload: init_with(),
                nodes: Vec::new(),
            };
            init_node(ids, fixed, &mut node, init_with);
            node
        })
        .collect();
    Root { nodes }
}

fn init_node<I, P, F>(ids: &[I], fixed: usize, into: &mut Node<I, P>, init_with: &F)
where
    I: Clone,
    F: Fn() -> P,
{
    for fixed in fixed + 1..ids.len() {
        let mut node = Node {
            id: ids[fixed].clone(),
            payload: init_with(),
            nodes: Vec::new(),
        };
        init_node(ids, fixed, &mut node, init_with);
        into.nodes.push(node);
    }
}

impl<I, P> Default for Root<I, P>
where
    I: Ord,
{
    fn default() -> Self {
        Root {
            nodes: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn create_empty() {
        let sample = Root::<u32, ()>::default();

        assert!(sample.is_empty());
    }

    #[test]
    fn bogus() {
        let sample = Root::<u32, ()>::default();
        let expected = Root::new(&[1, 2, 3]);

        assert_eq!(sample, expected);
    }

}
