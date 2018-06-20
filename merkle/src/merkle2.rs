use hash::{Algorithm, Hashable};
use proof2::Proof;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops;

/// Merkle Tree.
///
/// All leafs and nodes are stored in a linear array (vec).
///
/// A merkle tree is a tree in which every non-leaf node is the hash of its
/// children nodes. A diagram depicting how it works:
///
/// ```text
///         root = h1234 = h(h12 + h34)
///        /                           \
///  h12 = h(h1 + h2)            h34 = h(h3 + h4)
///   /            \              /            \
/// h1 = h(tx1)  h2 = h(tx2)    h3 = h(tx3)  h4 = h(tx4)
/// ```
///
/// In memory layout:
///
/// ```text
///     [h1 h2 h3 h4 h12 h34 root]
/// ```
///
/// Merkle root is always the last element in the array.
///
/// The number of inputs is not always a power of two which results in a
/// balanced tree structure as above.  In that case, parent nodes with no
/// children are also zero and parent nodes with only a single left node
/// are calculated by concatenating the left node with itself before hashing.
/// Since this function uses nodes that are pointers to the hashes, empty nodes
/// will be nil.
///
/// TODO: Ord
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct MerkleTree<T: Ord + Clone + AsRef<[u8]>, A: Algorithm<T>> {
    data: Vec<T>,
    layers: Vec<Vec<T>>, // TODO: redundant with data
    leafs: usize,
    height: usize,
    _a: PhantomData<A>,
}

impl<T: Ord + Clone + AsRef<[u8]>, A: Algorithm<T>> MerkleTree<T, A> {
    /// Creates new merkle from a sequence of hashes.
    pub fn new<I: IntoIterator<Item = T>>(data: I) -> MerkleTree<T, A> {
        Self::from_iter(data)
    }

    /// Creates new merkle tree from a list of hashable objects.
    pub fn from_data<O: Hashable<A>, I: IntoIterator<Item = O>>(data: I) -> MerkleTree<T, A> {
        let mut a = A::default();
        Self::from_iter(data.into_iter().map(|x| {
            a.reset();
            x.hash(&mut a);
            a.hash()
        }))
    }

    fn combine_hash(alg: &mut A, first: &T, second: Option<&T>, height: usize) -> T {
        alg.reset();
        if second.is_none() {
            return first.to_owned();
        }
        return alg.node(first.clone(), second.unwrap().clone(), height);
    }

    fn build_next_layer(alg: &mut A, prev_layer: &[T], height: usize) -> Vec<T> {
        prev_layer.chunks(2).fold(Vec::new(), |mut acc, pair| {
            acc.push(Self::combine_hash(
                alg,
                pair.first().unwrap(),
                pair.get(1),
                height,
            ));
            acc
        })
    }

    fn build(&mut self) {
        let mut a = A::default();
        let mut layers: Vec<Vec<T>> = Vec::new();
        layers.push(self.data.clone());

        while layers[layers.len() - 1].len() > 1 {
            let height = layers.len() - 1;
            let new_layer = Self::build_next_layer(&mut a, &layers[height], height);
            layers.push(new_layer);
        }

        self.layers = layers;
        self.data = Vec::new();
        for layer in self.layers.iter() {
            for element in layer {
                self.data.push(element.clone());
            }
        }
    }

    fn get_pair_element(idx: usize, layer: &[T]) -> Option<&T> {
        let pair_idx = match idx % 2 {
            0 => idx + 1,
            _ => idx - 1,
        };

        layer.get(pair_idx)
    }

    /// Generate merkle tree inclusion proof for leaf `i`
    pub fn gen_proof(&self, i: usize) -> Proof<T> {
        let mut idx = i;
        let mut lemma: Vec<T> = Vec::with_capacity(self.height + 1); // path + root
        lemma.push(self.data[i].clone());

        for layer in self.layers.iter() {
            let pair_element = Self::get_pair_element(idx, layer);

            if let Some(element) = pair_element {
                lemma.push(element.clone());
            }

            idx = idx / 2;
        }

        // root is final
        lemma.push(self.root());
        Proof::new(lemma, Vec::new())
    }

    /// Returns merkle root
    pub fn root(&self) -> T {
        self.data[self.data.len() - 1].clone()
    }

    /// Returns number of elements in the tree.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns `true` if the vector contains no elements.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Returns height of the tree
    pub fn height(&self) -> usize {
        self.height
    }

    /// Returns original number of elements the tree was built upon.
    pub fn leafs(&self) -> usize {
        self.leafs
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    pub fn as_slice(&self) -> &[T] {
        self
    }
}

impl<T: Ord + Clone + AsRef<[u8]>, A: Algorithm<T>> FromIterator<T> for MerkleTree<T, A> {
    /// Creates new merkle tree from an iterator over hashable objects.
    fn from_iter<I: IntoIterator<Item = T>>(into: I) -> Self {
        let iter = into.into_iter();
        let mut data: Vec<T> = match iter.size_hint().1 {
            Some(e) => {
                let pow = next_pow2(e);
                let size = 2 * pow - 1;
                Vec::with_capacity(size)
            }
            None => Vec::new(),
        };

        // leafs
        let mut a = A::default();
        for item in iter {
            a.reset();
            data.push(a.leaf(item));
        }

        data.sort();
        let leafs = data.len();
        let pow = next_pow2(leafs);
        let size = 2 * pow - 1;

        assert!(leafs > 1);

        let mut mt: MerkleTree<T, A> = MerkleTree {
            data,
            layers: Vec::new(),
            leafs,
            height: log2_pow2(size + 1),
            _a: PhantomData,
        };

        mt.build();
        mt
    }
}

impl<T: Ord + Clone + AsRef<[u8]>, A: Algorithm<T>> ops::Deref for MerkleTree<T, A> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.data.deref()
    }
}

/// `next_pow2` returns next highest power of two from a given number if
/// it is not already a power of two.
///
/// [](http://locklessinc.com/articles/next_pow2/)
/// [](https://stackoverflow.com/questions/466204/rounding-up-to-next-power-of-2/466242#466242)
pub fn next_pow2(mut n: usize) -> usize {
    n -= 1;
    n |= n >> 1;
    n |= n >> 2;
    n |= n >> 4;
    n |= n >> 8;
    n |= n >> 16;
    n |= n >> 32;
    n + 1
}

/// find power of 2 of a number which is power of 2
pub fn log2_pow2(n: usize) -> usize {
    n.trailing_zeros() as usize
}
