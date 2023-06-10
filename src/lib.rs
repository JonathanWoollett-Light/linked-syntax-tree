#![warn(clippy::pedantic)]

use std::alloc;
use std::ptr;
use std::ptr::NonNull;

/// A doubly-linked syntax tree.
///
/// E.g.
/// ```text
/// x = -10
/// loop
///     x = x + 1
///     if x
///         break
/// x = 2
/// ```
/// can be represented as:
/// ```text
/// ┌──────────┐
/// │x = -10   │
/// └──────────┘
/// │
/// ┌──────────┐
/// │loop      │
/// └──────────┘
/// │           ╲
/// ┌──────────┐ ┌─────────┐
/// │x = 2     │ │x = x + 1│
/// └──────────┘ └─────────┘
///              │
///              ┌─────────┐
///              │if x     │
///              └─────────┘
///                         ╲
///                          ┌─────────┐
///                          │break    │
///                          └─────────┘
/// ```
#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub struct SyntaxTree<T> {
    root: Option<NonNull<Node<T>>>,
}

impl<T> SyntaxTree<T> {
    /// Provides a cursor at the front element.
    #[must_use]
    pub fn cursor(&self) -> Cursor<'_, T> {
        Cursor {
            previous: None,
            current: self.root,
            tree: self,
        }
    }

    /// Provides a cursor with editing operation at the root element.
    pub fn cursor_mut(&mut self) -> CursorMut<'_, T> {
        CursorMut {
            previous: None,
            current: self.root,
            tree: self,
        }
    }

    /// Returns the length of the `SyntaxTree`.
    ///
    /// This operation should compute in *O*(n) time.
    #[must_use]
    pub fn len(&self) -> usize {
        self.iter().count()
    }

    /// Returns true if the tree contains no elements.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.root.is_some()
    }

    /// Returns a depth-first iterator with references.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        let stack = if let Some(root) = self.root {
            vec![root]
        } else {
            Vec::new()
        };
        Iter {
            stack,
            __marker: self,
        }
    }

    /// Returns a depth-first iterator with mutable references.
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        let stack = if let Some(root) = self.root {
            vec![root]
        } else {
            Vec::new()
        };
        IterMut {
            stack,
            __marker: self,
        }
    }
}
impl<T> Default for SyntaxTree<T> {
    fn default() -> Self {
        Self { root: None }
    }
}
impl<T: Clone> Clone for SyntaxTree<T> {
    fn clone(&self) -> Self {
        if let Some(root) = self.root {
            unsafe {
                let root_ptr = {
                    let ptr: *mut Node<T> =
                        alloc::alloc(alloc::Layout::new::<Node<T>>()).cast::<Node<T>>();
                    ptr::copy_nonoverlapping(root.as_ptr(), ptr, 1);
                    NonNull::new(ptr).unwrap()
                };

                // TODO Like the other cases, this will only ever be 2 elements make this more efficient.
                let mut stack = vec![root_ptr];
                while let Some(mut current) = stack.pop() {
                    if let Some(next) = &mut current.as_mut().next {
                        let next_ptr = {
                            let ptr =
                                alloc::alloc(alloc::Layout::new::<Node<T>>()).cast::<Node<T>>();
                            ptr::copy_nonoverlapping(next.as_ptr(), ptr, 1);
                            NonNull::new(ptr).unwrap()
                        };
                        *next = next_ptr;
                        stack.push(next_ptr);
                    }
                    if let Some(child) = &mut current.as_mut().child {
                        let child_ptr = {
                            let ptr =
                                alloc::alloc(alloc::Layout::new::<Node<T>>()).cast::<Node<T>>();
                            ptr::copy_nonoverlapping(child.as_ptr(), ptr, 1);
                            NonNull::new(ptr).unwrap()
                        };
                        *child = child_ptr;
                        stack.push(child_ptr);
                    }
                }

                Self {
                    root: Some(root_ptr),
                }
            }
        } else {
            Self { root: None }
        }
    }
}

/// Iterates through elements depth-first in a [`SyntaxTree`] returning references.
pub struct Iter<'a, T> {
    stack: Vec<NonNull<Node<T>>>,
    __marker: &'a SyntaxTree<T>,
}
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        let current_opt = self.stack.pop();
        unsafe {
            if let Some(current) = current_opt {
                if let Some(next) = current.as_ref().next {
                    self.stack.push(next);
                }
                if let Some(child) = current.as_ref().child {
                    self.stack.push(child);
                }
                Some(&current.as_ref().element)
            } else {
                None
            }
        }
    }
}

/// Iterates through elements depth-first in a [`SyntaxTree`] returning mutable references.
pub struct IterMut<'a, T> {
    stack: Vec<NonNull<Node<T>>>,
    __marker: &'a mut SyntaxTree<T>,
}
impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<Self::Item> {
        let current_opt = self.stack.pop();
        unsafe {
            if let Some(current) = current_opt {
                if let Some(next) = current.as_ref().next {
                    self.stack.push(next);
                }
                if let Some(child) = current.as_ref().child {
                    self.stack.push(child);
                }
            }
            current_opt.map(|mut c| &mut c.as_mut().element)
        }
    }
}

/// Roughly matches [`std::collections::linked_list::Cursor`].
pub struct Cursor<'a, T> {
    previous: Option<NonNull<Node<T>>>,
    current: Option<NonNull<Node<T>>>,
    tree: &'a SyntaxTree<T>,
}
impl<T> Cursor<'_, T> {
    /// Provides a reference to the root element.
    #[must_use]
    pub fn root(&self) -> Option<&T> {
        self.tree.root.map(|r| unsafe { &r.as_ref().element })
    }

    /// Get the current element.
    #[must_use]
    pub fn current(&self) -> Option<&T> {
        self.current.map(|ptr| unsafe { &ptr.as_ref().element })
    }

    /// Moves the cursor to predecessor element.
    ///
    /// If there is no previous value, the cursor is not moved.
    pub fn move_pred(&mut self) {
        if let Some(previous) = self.previous {
            self.current = Some(previous);
            let opt = unsafe { previous.as_ref().predecessor.as_ref() };
            self.previous = opt.map(|p| *p.as_ref().unwrap());
        }
    }

    /// Moves the cursor to the next element.
    pub fn move_next(&mut self) {
        if let Some(current) = self.current {
            self.previous = Some(current);
            let opt = unsafe { current.as_ref().next.as_ref() };
            self.current = opt.copied();
        }
    }

    /// Returns a reference to the next element.
    #[must_use]
    pub fn peek_next(&self) -> Option<&T> {
        if let Some(current) = self.current {
            unsafe { current.as_ref().next.map(|n| &n.as_ref().element) }
        } else {
            None
        }
    }

    /// Returns a reference to the predecessor element.
    #[must_use]
    pub fn peek_prev(&self) -> Option<&T> {
        self.previous.map(|p| unsafe { &p.as_ref().element })
    }

    /// Returns a reference to the child element.
    #[must_use]
    pub fn peek_child(&self) -> Option<&T> {
        if let Some(current) = self.current {
            unsafe { current.as_ref().child.map(|n| &n.as_ref().element) }
        } else {
            None
        }
    }
}

impl<'a, T> std::ops::Deref for CursorMut<'a, T> {
    type Target = Cursor<'a, T>;

    fn deref(&self) -> &Self::Target {
        // Is this safe? I don't know, but it sure avoids code duplication.
        unsafe { &*(self as *const CursorMut<'_, T>).cast() }
    }
}

impl<'a, T> std::ops::DerefMut for CursorMut<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Is this safe? I don't know, but it sure avoids code duplication.
        unsafe { &mut *(self as *mut CursorMut<'_, T>).cast() }
    }
}

/// Roughly matches [`std::collections::linked_list::CursorMut`].
#[derive(Debug)]
pub struct CursorMut<'a, T> {
    previous: Option<NonNull<Node<T>>>,
    current: Option<NonNull<Node<T>>>,
    tree: &'a mut SyntaxTree<T>,
}
impl<T> CursorMut<'_, T> {
    /// Provides a mutable reference to the root element.
    pub fn root_mut(&mut self) -> Option<&mut T> {
        self.tree
            .root
            .map(|mut r| unsafe { &mut r.as_mut().element })
    }

    /// Get the current element.
    pub fn current_mut(&mut self) -> Option<&mut T> {
        self.current
            .map(|mut ptr| unsafe { &mut ptr.as_mut().element })
    }

    /// Inserts an element before the current element.
    ///
    /// If the cursor has `None` current element it is set to the inserted element.
    pub fn insert_before(&mut self, item: T) {
        let ptr = unsafe { alloc::alloc(alloc::Layout::new::<Node<T>>()).cast::<Node<T>>() };
        match (self.current, self.previous) {
            (Some(mut current), Some(mut previous)) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        predecessor: Some(Predecessor::Previous(previous)),
                        child: None,
                        next: Some(current),
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                previous.as_mut().next = Some(ptr);
                current.as_mut().predecessor = Some(Predecessor::Previous(ptr));
                self.previous = Some(ptr);
            },
            (Some(mut current), None) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        predecessor: None,
                        child: None,
                        next: Some(current),
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                current.as_mut().predecessor = Some(Predecessor::Previous(ptr));
                self.previous = Some(ptr);
                self.tree.root = Some(ptr);
            },
            (None, Some(mut previous)) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        predecessor: Some(Predecessor::Previous(previous)),
                        child: None,
                        next: None,
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                previous.as_mut().next = Some(ptr);
                self.current = Some(ptr);
            },
            (None, None) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        predecessor: None,
                        child: None,
                        next: None,
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                self.current = Some(ptr);
                self.tree.root = Some(ptr);
            },
        }
    }

    /// Inserts an element after the current element.
    ///
    /// If the cursor has `None` current element it is set to the inserted element.
    pub fn insert_after(&mut self, item: T) {
        let ptr = unsafe { alloc::alloc(alloc::Layout::new::<Node<T>>()).cast::<Node<T>>() };
        match (self.current, self.previous) {
            (Some(mut current), _) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        predecessor: Some(Predecessor::Previous(current)),
                        child: None,
                        next: current.as_ref().next,
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                if let Some(mut next) = current.as_ref().next {
                    next.as_mut().predecessor = Some(Predecessor::Previous(ptr));
                }
                current.as_mut().next = Some(ptr);
            },
            (None, Some(mut previous)) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        predecessor: Some(Predecessor::Previous(previous)),
                        child: None,
                        next: None,
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                previous.as_mut().next = Some(ptr);
                self.current = Some(ptr);
            },
            (None, None) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        predecessor: None,
                        child: None,
                        next: None,
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                self.current = Some(ptr);
                self.tree.root = Some(ptr);
            },
        }
    }

    /// Removes the current node.
    ///
    /// When removing a node with a child node, this child node is removed.
    pub fn remove_current(&mut self) {
        match (self.current, self.previous) {
            (Some(current), Some(mut previous)) => unsafe {
                self.current = current.as_ref().next;
                previous.as_mut().next = current.as_ref().next;
                if let Some(mut next) = current.as_ref().next {
                    next.as_mut().predecessor = Some(Predecessor::Previous(previous));
                }

                // Deallocate all child nodes of the old current node.
                if let Some(child) = current.as_ref().child {
                    // TODO This will never be greater than 2 elements, do something more
                    // performant.
                    let mut stack = vec![child];
                    while let Some(next) = stack.pop() {
                        if let Some(child) = next.as_ref().child {
                            stack.push(child);
                        }
                        if let Some(next) = next.as_ref().next {
                            stack.push(next);
                        }
                        alloc::dealloc(next.as_ptr().cast(), alloc::Layout::new::<Node<T>>());
                    }
                }
                alloc::dealloc(current.as_ptr().cast(), alloc::Layout::new::<Node<T>>());
            },
            (Some(current), None) => unsafe {
                self.current = current.as_ref().next;
                self.tree.root = current.as_ref().next;
                if let Some(mut next) = current.as_ref().next {
                    next.as_mut().predecessor = None;
                }

                // Deallocate all child nodes of the old current node.
                if let Some(child) = current.as_ref().child {
                    // TODO This will never be greater than 2 elements, do something more
                    // performant.
                    let mut stack = vec![child];
                    while let Some(next) = stack.pop() {
                        if let Some(child) = next.as_ref().child {
                            stack.push(child);
                        }
                        if let Some(next) = next.as_ref().next {
                            stack.push(next);
                        }
                        alloc::dealloc(next.as_ptr().cast(), alloc::Layout::new::<Node<T>>());
                    }
                }
                alloc::dealloc(current.as_ptr().cast(), alloc::Layout::new::<Node<T>>());
            },
            (None, _) => {}
        }
    }

    /// Inserts the elements from the given `SyntaxTree` after the current one.
    ///
    /// If the current element is `None` it becomes the root element from the given `SyntaxTree`.
    // It would be unsafe to modifier the passed `tree`, as a mutable cursor on `self` may modify it
    // at the same time
    #[allow(clippy::needless_pass_by_value)]
    pub fn splice_after(&mut self, tree: SyntaxTree<T>) {
        match (self.current, self.previous) {
            (Some(mut current), _) => unsafe {
                match (current.as_ref().next, tree.root) {
                    (Some(mut self_next), Some(mut tree_root)) => {
                        // Finds the last element in `tree`.
                        let mut tree_last = tree_root;
                        while let Some(next) = tree_last.as_ref().next {
                            tree_last = next;
                        }
                        tree_last.as_mut().next = Some(self_next);
                        self_next.as_mut().predecessor = Some(Predecessor::Previous(tree_last));
                        tree_root.as_mut().predecessor = Some(Predecessor::Previous(current));
                        current.as_mut().next = tree.root;
                    }
                    (None, Some(mut tree_root)) => {
                        tree_root.as_mut().predecessor = Some(Predecessor::Previous(current));
                        current.as_mut().next = tree.root;
                    }
                    (_, None) => {}
                }
            },
            (None, Some(mut previous)) => unsafe {
                if let Some(mut tree_root) = tree.root {
                    self.current = Some(tree_root);
                    previous.as_mut().next = Some(tree_root);
                    tree_root.as_mut().predecessor = Some(Predecessor::Previous(previous));
                }
            },
            (None, None) => {
                self.current = tree.root;
                self.tree.root = tree.root;
            }
        }
    }

    /// Inserts the elements from the given `SyntaxTree` before the current one.
    ///
    /// If the current element is `None` it becomes the root element from the given `SyntaxTree`.
    // It would be unsafe to modifier the passed `tree`, as a mutable cursor on `self` may modify it
    // at the same time
    #[allow(clippy::needless_pass_by_value)]
    pub fn splice_before(&mut self, tree: SyntaxTree<T>) {
        match (self.current, self.previous) {
            (Some(mut current), Some(mut previous)) => unsafe {
                if let Some(tree_root) = tree.root {
                    // Finds the last element in `tree`.
                    let mut tree_last = tree_root;
                    while let Some(next) = tree_last.as_ref().next {
                        tree_last = next;
                    }
                    tree_last.as_mut().next = Some(current);
                    current.as_mut().predecessor = Some(Predecessor::Previous(tree_last));
                    self.previous = Some(tree_last);
                    previous.as_mut().next = Some(tree_root);
                }
            },
            (Some(mut current), None) => unsafe {
                if let Some(tree_root) = tree.root {
                    // Finds the last element in `tree`.
                    let mut tree_last = tree_root;
                    while let Some(next) = tree_last.as_ref().next {
                        tree_last = next;
                    }
                    tree_last.as_mut().next = Some(current);
                    current.as_mut().predecessor = Some(Predecessor::Previous(tree_last));
                    self.previous = Some(tree_last);
                    self.tree.root = Some(tree_root);
                }
            },
            (None, Some(mut previous)) => unsafe {
                if let Some(mut tree_root) = tree.root {
                    self.current = Some(tree_root);
                    previous.as_mut().next = Some(tree_root);
                    tree_root.as_mut().predecessor = Some(Predecessor::Previous(previous));
                }
            },
            (None, None) => {
                self.current = tree.root;
                self.tree.root = tree.root;
            }
        }
    }

    /// Splits the list into two after the current element. This will return a new list consisting
    /// of everything after the cursor, with the original list retaining everything before.
    pub fn split_after(&mut self) -> SyntaxTree<T> {
        match (self.current, self.previous) {
            (Some(mut current), _) => unsafe {
                if let Some(next) = current.as_ref().next {
                    current.as_mut().next = None;
                    SyntaxTree { root: Some(next) }
                } else {
                    SyntaxTree { root: None }
                }
            },
            (None, _) => SyntaxTree { root: None },
        }
    }

    /// Splits the list into two before the current element. This will return a new list consisting
    /// of everything before the cursor, with the original list retaining everything after.
    pub fn split_before(&mut self) -> SyntaxTree<T> {
        match (self.current, self.previous) {
            (Some(mut current), Some(mut previous)) => unsafe {
                previous.as_mut().next = None;
                self.previous = None;
                current.as_mut().predecessor = None;

                let temp = SyntaxTree {
                    root: self.tree.root,
                };
                self.tree.root = Some(current);
                temp
            },
            (None, Some(mut previous)) => unsafe {
                previous.as_mut().next = None;
                self.previous = None;

                let temp = SyntaxTree {
                    root: self.tree.root,
                };
                self.tree.root = None;
                temp
            },
            (_, None) => SyntaxTree { root: None },
        }
    }
}

/// A statement in an AST may have:
/// - A previous statement
/// - A next statement
/// - A child statement
/// - A parent statement
///
/// Consider the example:
/// ```text
/// x = -10
/// loop
///     x = x + 1
///     if x
///         break
/// x = 2
/// ```
/// this can be represented as:
/// ```text
/// ┌──────────┐
/// │x = -10   │
/// └──────────┘
/// │
/// ┌──────────┐
/// │loop      │
/// └──────────┘
/// │           ╲
/// ┌──────────┐ ┌─────────┐
/// │x = 2     │ │x = x + 1│
/// └──────────┘ └─────────┘
///              │
///              ┌─────────┐
///              │if x     │
///              └─────────┘
///                         ╲
///                          ┌─────────┐
///                          │break    │
///                          └─────────┘
/// ```
/// this is a simplified tree structure.
#[derive(Debug)]
enum Predecessor<T> {
    Parent(T),
    Previous(T),
}
impl<T> Predecessor<T> {
    fn unwrap(self) -> T {
        match self {
            Self::Previous(x) | Self::Parent(x) => x,
        }
    }
    fn as_ref(&self) -> Predecessor<&T> {
        match self {
            Self::Parent(x) => Predecessor::Parent(x),
            Self::Previous(x) => Predecessor::Previous(x),
        }
    }
    // fn as_mut(&mut self) -> Predecessor<&mut T> {
    //     match self {
    //         Self::Parent(x) => Predecessor::Parent(x),
    //         Self::Previous(x) => Predecessor::Previous(x),
    //     }
    // }
}

#[derive(Debug)]
struct Node<T> {
    element: T,
    predecessor: Option<Predecessor<NonNull<Node<T>>>>,
    child: Option<NonNull<Node<T>>>,
    next: Option<NonNull<Node<T>>>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_before() {
        let mut tree = SyntaxTree::<u8>::default();
        let mut cursor = tree.cursor_mut();
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_before(1);
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_before(2);
        assert_eq!(cursor.peek_prev(), Some(&2));
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&1));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&1));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), Some(&2));
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), Some(&1));

        cursor.insert_before(3);
        assert_eq!(cursor.peek_prev(), Some(&3));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), Some(&1));

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&2));
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&1));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&1));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), Some(&2));
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), Some(&3));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), Some(&1));

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));
    }

    #[test]
    fn insert_after() {
        let mut tree = SyntaxTree::<u8>::default();
        let mut cursor = tree.cursor_mut();
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_after(1);
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_after(2);
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&1));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&2));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), Some(&1));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.insert_after(3);
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&3));

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&1));
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&3));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&2));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&2));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), Some(&3));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), Some(&1));
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&3));

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&3));
    }

    #[test]
    fn remove() {
        let mut tree = SyntaxTree::<u8>::default();
        let mut cursor = tree.cursor_mut();
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_after(1);
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_after(2);
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.insert_after(3);
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&3));

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&1));
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_next();
        assert_eq!(cursor.peek_prev(), Some(&3));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), Some(&1));
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_pred();
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&3));

        cursor.remove_current();
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.remove_current();
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);
    }

    #[test]
    fn clone() {
        let mut tree = SyntaxTree::<u8>::default();
        let mut cursor = tree.cursor_mut();
        cursor.insert_after(1);
        cursor.insert_before(2);
        cursor.insert_after(3);
        cursor.insert_before(4);
        cursor.insert_after(5);

        let tree_clone = tree.clone();
        tree.iter().zip(tree_clone.iter()).all(|(a, b)| a == b);
    }

    #[test]
    fn indexing() {
        let mut tree = SyntaxTree::<u8>::default();
        let mut iter = tree.iter();
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(tree.len(), 0);

        tree.cursor_mut().insert_after(1);
        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(tree.len(), 1);

        tree.cursor_mut().insert_before(2);
        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(tree.len(), 2);

        tree.cursor_mut().insert_after(3);
        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(tree.len(), 3);

        tree.cursor_mut().insert_before(4);
        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(tree.len(), 4);

        tree.cursor_mut().insert_after(5);
        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), Some(&5));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
        assert_eq!(tree.len(), 5);
    }

    #[test]
    fn splice_and_split_after() {
        let mut tree_one = SyntaxTree::<u8>::default();
        let mut cursor_one = tree_one.cursor_mut();
        cursor_one.insert_after(1);
        cursor_one.insert_after(2);
        cursor_one.insert_after(3);

        let mut tree_two = SyntaxTree::<u8>::default();
        let mut cursor_two = tree_two.cursor_mut();
        cursor_two.insert_after(4);
        cursor_two.insert_after(5);
        cursor_two.insert_after(6);

        cursor_one.splice_after(tree_two);

        // Its easier to use the iterator to compare here.
        let mut iter = tree_one.iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), Some(&6));
        assert_eq!(iter.next(), Some(&5));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);

        let mut cursor = tree_one.cursor_mut();
        cursor.move_next();
        cursor.move_next();
        let tree_three = cursor.split_after();
        let mut iter = tree_one.iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), Some(&6));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);

        let mut iter = tree_three.iter();
        assert_eq!(iter.next(), Some(&5));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }
    #[test]
    fn splice_and_split_before() {
        let mut tree_one = SyntaxTree::<u8>::default();
        let mut cursor_one = tree_one.cursor_mut();
        cursor_one.insert_after(1);
        cursor_one.insert_after(2);
        cursor_one.insert_after(3);

        let mut tree_two = SyntaxTree::<u8>::default();
        let mut cursor_two = tree_two.cursor_mut();
        cursor_two.insert_after(4);
        cursor_two.insert_after(5);
        cursor_two.insert_after(6);

        cursor_one.splice_before(tree_two);

        // Its easier to use the iterator to compare here.
        let mut iter = tree_one.iter();
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), Some(&6));
        assert_eq!(iter.next(), Some(&5));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);

        let mut cursor = tree_one.cursor_mut();
        cursor.move_next();
        cursor.move_next();
        cursor.move_next();
        let tree_three = cursor.split_before();
        let mut iter = tree_one.iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);

        let mut iter = tree_three.iter();
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), Some(&6));
        assert_eq!(iter.next(), Some(&5));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }
}
