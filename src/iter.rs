//! Iterator utilities

use std::{cell::RefCell, rc::Rc};

use num::BigInt;

/// A singleton iterator
///
/// Returns a single item and then exhausts
///
/// # Example
///
/// ```rust
/// use gosper::iter::Once;
///
/// let mut iter = Once::from(10);
///
/// assert_eq!(iter.next(), Some(10));
/// assert_eq!(iter.next(), None);
/// assert_eq!(iter.next(), None);
/// ```
pub struct Once<T>(Option<T>);

impl<T> From<T> for Once<T> {
    fn from(value: T) -> Self {
        Self(Some(value))
    }
}

impl<T> Iterator for Once<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.take()
    }
}

///  Converts iterator of integers to [`BigInt`]s
///
///  Like an iterator map closure but a concrete typed
pub struct ToBigInts<I>(pub I);

impl<I> Iterator for ToBigInts<I>
where
    I: Iterator,
    BigInt: From<I::Item>,
{
    type Item = BigInt;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(BigInt::from)
    }
}

/// An iterator wrapper with shared memoization
///
/// Generates new [`MemoIter`] iterators.
///
/// # Example
///
/// [`Memo`]s produce [`Clone`]s of items from the wrapped iterator.
///
/// ```rust
/// use gosper::iter::Memo;
///
/// let memo = Memo::new([0, 1, 2].into_iter());
///
/// assert!(memo.iter().eq([0, 1, 2].into_iter()));
/// assert!(memo.iter().eq([0, 1, 2].into_iter()));
/// assert!(memo.clone().iter().eq([0, 1, 2].into_iter()));
/// ```
///
/// [`MemoIter`] works like [`std::slice::Iter`] in that it does not consume
/// self. In this example, we create a counter iterator and iterate over the
/// items multiple times.
///
/// ```rust
/// # use gosper::iter::Memo;
/// use std::iter::from_fn;
///
/// let mut count = 0;
/// let memo = Memo::from(from_fn(|| {
///     count += 1;
///     Some(count)
/// }));
///
/// assert!(memo.iter().take(5).eq([1, 2, 3, 4, 5].into_iter()));
/// assert!(memo.iter().take(3).eq([1, 2, 3].into_iter()));
/// assert_eq!(count, 5);
/// ```
///
/// [`Memo`] also implements the [`IntoIterator`] interface which **does**
/// consume self, so be aware of moves.
///
/// ```rust, compile_fail
/// # use gosper::iter::Memo;
/// let memo = Memo::from([0, 1, 2]);
///
/// let mut cloned = memo.clone().into_iter(); // clone is fine
/// assert!(matches!(cloned.next(), Some(0)));
///
/// let mut moved = memo.into_iter(); // move occurs here
/// assert!(matches!(moved.next(), Some(0)));
///
/// let mut use_after_move = memo.into_iter(); // won't compile!
/// assert!(matches!(use_after_move.next(), Some(0)));
/// ```
pub struct Memo<I>
where
    I: Iterator,
{
    iterator: Rc<RefCell<Option<I>>>,
    memo: Rc<RefCell<Vec<I::Item>>>,
}

/// Clone the [`Rc`] without cloning the underlying iterator
impl<I: Iterator> Clone for Memo<I> {
    fn clone(&self) -> Self {
        Self {
            iterator: self.iterator.clone(),
            memo: self.memo.clone(),
        }
    }
}

impl<I> Memo<I>
where
    I: Iterator,
{
    pub fn new(iter: I) -> Self {
        Self {
            iterator: Rc::new(RefCell::new(Some(iter))),
            memo: Rc::new(RefCell::new(Vec::new())),
        }
    }

    /// Returns a new [`MemoIter`] instance that will used the shared
    /// memoization cache.
    pub fn iter(&self) -> MemoIter<I> {
        MemoIter {
            index: 0,
            memo: self.clone(),
        }
    }
}

/// An iterator that uses a shared memoization cache.
///
/// See [`Memo`] and [`Memo::iter()`]
///
/// Iterators of this type will store items from the shared [`Iterator`] in a
/// [`Vec`]. New instances of this struct will emit items from the shared
/// [`Vec`] if available, then extend the `Vec` with further items as they are
/// read from the `Iterator`.
///
/// This allows you to iterate over the same items several times without
/// reconstructing them. If items from the iterator are expensive to compute,
/// for instance, this iterator will ensure they are computed at most once.
pub struct MemoIter<I>
where
    I: Iterator,
{
    index: usize,
    memo: Memo<I>,
}

impl<I> Iterator for MemoIter<I>
where
    I: Iterator,
    I::Item: Clone,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        // use memo value if available
        {
            if let Some(i) = self.memo.memo.borrow().get(self.index) {
                self.index += 1;
                return Some(i.clone());
            }
        }

        // read next value from iterator if available and store it in the memo
        {
            let mut iterator_option = self.memo.iterator.borrow_mut();
            if let Some(iter) = iterator_option.as_mut() {
                if let Some(i) = iter.next() {
                    self.index += 1;
                    self.memo.memo.borrow_mut().push(i.clone());
                    return Some(i);
                } else {
                    // drop iterator
                    iterator_option.take();
                    return None;
                }
            }
        }

        // otherwise none
        None
    }
}

impl<I> IntoIterator for Memo<I>
where
    I: Iterator,
    I::Item: Clone,
{
    type IntoIter = MemoIter<I>;
    type Item = I::Item;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<I> From<I> for Memo<I::IntoIter>
where
    I: IntoIterator,
{
    fn from(into: I) -> Self {
        Self::new(into.into_iter())
    }
}
