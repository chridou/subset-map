pub type Nodes<I, P> = Vec<Node<I, P>>;

pub struct Root<I, P> {
    pub nodes: Nodes<I, P>,
}

pub struct Node<I, P> {
    pub id: I,
    pub payload: P,
    pub nodes: Nodes<I, P>,
}

impl<I, P> Root<I, P> {}

impl<I, P> Default for Root<I, P> {
    fn default() -> Self {
        Root {
            nodes: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
