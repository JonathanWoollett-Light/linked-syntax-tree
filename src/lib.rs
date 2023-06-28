#![warn(clippy::pedantic, missing_debug_implementations, missing_docs)]

//! A doubly-linked syntax tree.
//!
//! Offers functionality similar to [`std::collections::LinkedList`](https://doc.rust-lang.org/std/collections/struct.LinkedList.html).
//!
//! ## Example
//!
//! ```text
//! x = -10
//! loop
//!     x = x + 1
//!     if x
//!         break
//! x = 2
//! ```
//!
//! can be represented as:
//!
//! ```text
//! ┌──────────┐
//! │x = -10   │
//! └──────────┘
//! │
//! ┌──────────┐
//! │loop      │
//! └──────────┘
//! │           ╲
//! ┌──────────┐ ┌─────────┐
//! │x = 2     │ │x = x + 1│
//! └──────────┘ └─────────┘
//!              │
//!              ┌─────────┐
//!              │if x     │
//!              └─────────┘
//!                         ╲
//!                          ┌─────────┐
//!                          │break    │
//!                          └─────────┘
//! ```
//! which can be constructed with:
//! ```rust
//! # use linked_syntax_tree::*;
//! let mut root = SyntaxTree::default();
//! let mut cursor = root.cursor_mut();
//! cursor.insert_next("x = -10"); // Inserts "x = -10" as the root element.
//! cursor.insert_next("loop"); // Inserts "loop" as the next element.
//! cursor.move_next(); // Moves the cursor to "loop".
//! cursor.insert_child("x = x + 1"); // Inserts "x = x + 1" as the child element.
//! cursor.move_child(); // Moves the cursor to "x = x + 1".
//! cursor.insert_next("if x"); // Inserts "if x" as the next element.
//! cursor.move_next(); // Moves the cursor to "if x".
//! cursor.insert_child("break"); // Inserts "break" as the child element.
//! cursor.move_parent(); // Moves the cursor to "if x".
//! cursor.move_parent(); // Moves the cursor to "loop".
//! cursor.insert_next("x = 2");
//! assert_eq!(root.to_string(), r#"x = -10
//! loop
//!     x = x + 1
//!     if x
//!         break
//! x = 2
//! "#);
//! ```
//!
//! ## Terminology
//!
//! - **next**: `loop` is the *next* element of `x = -10`.
//! - **previous**: `x = -10` is the *previous* element of `loop`.
//! - **child**: `x = x + 1` is the *child* element of `loop`.
//! - **parent**: `loop` is the *parent* element of `x = x + 1`.
//! - **preceding**: All *previous* elements and *parent* elements are *preceding* elements.
//!   A *preceding* element may be a *previous* element or a *parent* element.
//! - **predecessor**: The previous element if the tree is flattened e.g. `break` is the
//!   *predecessor* of `x = 2`.
//! - **successor**: The next element if the tree is flattened e.g. `x = 2` is the *successor* of
//!   `break`.
//!
//! ## Use-case
//!
//! I'm using this to contain an AST for compile-time evaluation in my personal WIP language.

use std::alloc;
use std::fmt;
use std::ptr;
use std::ptr::NonNull;

/// A doubly linked syntax tree.
#[derive(Debug)]
pub struct SyntaxTree<T>(OptionalNode<T>);

type OptionalNode<T> = Option<NonNull<Node<T>>>;
type NodePredecessor<T> = Preceding<NonNull<Node<T>>>;

impl<T> PartialEq for SyntaxTree<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl<T> Eq for SyntaxTree<T> {}

/// The string used for depth in the [`SyntaxTree`] [`std::fmt::Display`] implementation.
pub const INDENT: &str = "    ";

impl<T: fmt::Display> fmt::Display for SyntaxTree<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for Element { item, depth } in self.iter() {
            writeln!(f, "{}{item}", INDENT.repeat(depth))?;
        }
        Ok(())
    }
}

impl<T> SyntaxTree<T> {
    /// Provides a cursor at the front element.
    #[must_use]
    pub fn cursor(&self) -> Cursor<T> {
        Cursor {
            preceding: None,
            current: self.0,
            root: &self.0,
            succeeding_bound: None,
        }
    }

    /// Provides a cursor with editing operation at the root element.
    pub fn cursor_mut(&mut self) -> CursorMut<T> {
        CursorMut {
            preceding: None,
            current: self.0,
            root: &mut self.0,
        }
    }

    /// Returns the length of the `OptionalNode`.
    ///
    /// This operation should compute in *O*(n) time.
    #[must_use]
    pub fn len(&self) -> usize {
        self.iter().count()
    }

    /// Returns true if the tree contains no elements.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_some()
    }

    /// Returns a depth-first iterator with references.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        let stack = if let Some(root) = self.0 {
            vec![(root, 0)]
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
        let stack = if let Some(root) = self.0 {
            vec![(root, 0)]
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
        Self(None)
    }
}
impl<T: Clone> Clone for SyntaxTree<T> {
    fn clone(&self) -> Self {
        if let Some(root) = self.0 {
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

                Self(Some(root_ptr))
            }
        } else {
            Self(None)
        }
    }
}
impl<T> From<T> for SyntaxTree<T> {
    fn from(element: T) -> Self {
        let ptr = unsafe {
            let ptr = alloc::alloc(alloc::Layout::new::<Node<T>>()).cast();
            ptr::write(
                ptr,
                Node {
                    element,
                    preceding: None,
                    child: None,
                    next: None,
                },
            );
            NonNull::new_unchecked(ptr)
        };
        Self(Some(ptr))
    }
}
impl<T> Drop for SyntaxTree<T> {
    fn drop(&mut self) {
        if let Some(current) = self.0 {
            let mut stack = vec![current];
            // Deallocate all child nodes of the old current node.
            unsafe {
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
        }
    }
}

/// Iterates through elements depth-first in a [`OptionalNode`] returning references.
#[derive(Debug)]
pub struct Iter<'a, T> {
    stack: Vec<(NonNull<Node<T>>, usize)>,
    __marker: &'a SyntaxTree<T>,
}
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = Element<&'a T>;
    fn next(&mut self) -> Option<Self::Item> {
        let current_opt = self.stack.pop();
        unsafe {
            if let Some((current, depth)) = current_opt {
                if let Some(next) = current.as_ref().next {
                    self.stack.push((next, depth));
                }
                if let Some(child) = current.as_ref().child {
                    self.stack.push((child, depth + 1));
                }
                Some(Element {
                    item: &current.as_ref().element,
                    depth,
                })
            } else {
                None
            }
        }
    }
}

/// Iterates through elements depth-first in a [`OptionalNode`] returning mutable references.
#[derive(Debug)]
pub struct IterMut<'a, T> {
    stack: Vec<(NonNull<Node<T>>, usize)>,
    __marker: &'a mut SyntaxTree<T>,
}
impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = Element<&'a mut T>;
    fn next(&mut self) -> Option<Self::Item> {
        let current_opt = self.stack.pop();
        unsafe {
            if let Some((mut current, depth)) = current_opt {
                if let Some(next) = current.as_ref().next {
                    self.stack.push((next, depth));
                }
                if let Some(child) = current.as_ref().child {
                    self.stack.push((child, depth + 1));
                }
                Some(Element {
                    item: &mut current.as_mut().element,
                    depth,
                })
            } else {
                None
            }
        }
    }
}

/// An element in a [`OptionalNode`] with a known depth.
#[derive(Debug, Eq, PartialEq)]
pub struct Element<T> {
    /// The data within the node.
    pub item: T,
    /// The depth of the node.
    pub depth: usize,
}

/// A cursor which can be used to mutate element, but only in such a way that it does not remove
/// elements in `self.guarded_nodes`. This allows for a semi-mutable cursor on the upper portion of
/// a syntax tree while maintaining a mutable cursor on the lower portion.
#[derive(Debug)]
pub struct RestrictedCursor<'a, T> {
    /// The preceding element, mutably accessing this is unsafe.
    pub preceding: Option<NodePredecessor<T>>,
    /// The current element, mutably accessing this is unsafe.
    pub current: OptionalNode<T>,
    /// The current root element, mutably accessing this is unsafe.
    pub root: &'a mut OptionalNode<T>,
    /// The set of nodes which cannot be removed, mutably accessing this is unsafe.
    pub guarded_nodes: Vec<NonNull<Node<T>>>,
}
impl<'a, T> From<RestrictedCursor<'a, T>> for Cursor<'a, T> {
    fn from(cursor: RestrictedCursor<'a, T>) -> Cursor<'a, T> {
        Cursor {
            preceding: cursor.preceding,
            current: cursor.current,
            root: cursor.root,
            succeeding_bound: cursor.guarded_nodes.first().copied(),
        }
    }
}
impl<'a, T> RestrictedCursor<'a, T> {
    /// Get the current element.
    ///
    /// Returns `None` if the current element is `None` or if the current element is the lower bound.
    #[must_use]
    pub fn current(&self) -> Option<&T> {
        self.current.map(|ptr| unsafe { &ptr.as_ref().element })
    }

    /// Moves the cursor to the preceding element.
    ///
    /// If there is no preceding element the cursor is not moved.
    pub fn move_preceding(&mut self) {
        if let Some(preceding) = self.preceding {
            // If we move to a parent node, we add this parent to the guarded nodes to specify that
            // it cannot be removed (removing it would remove its children which would remove nodes
            // borrowed by a mutable cursor).
            if let Preceding::Parent(parent) = preceding {
                self.guarded_nodes.push(parent);
            }
            self.current = Some(preceding.unwrap());
            self.preceding = unsafe { preceding.unwrap().as_ref().preceding.as_ref().copied() };
        }
    }

    /// Moves the cursor to the next element if there is some current element and the next element
    /// is within the bounds of the cursor (when splitting a mutable cursor, an immutable cursor is
    /// produced where its bound restrict it to element above the mutable cursor).
    pub fn move_next(&mut self) {
        if let Some(current) = self.current {
            // We cannot move past the 1st guarded node (as all nodes past this are borrowed by a
            // mutable cursor).
            if Some(current) == self.guarded_nodes.first().copied() {
                return;
            }
            self.preceding = Some(Preceding::Previous(current));
            self.current = unsafe { current.as_ref().next };
        }
    }

    /// Moves the cursor to the child element if there is some current element and the child element
    /// is within the bounds of the cursor (when splitting a mutable cursor, an immutable cursor is
    /// produced where its bound restrict it to element above the mutable cursor).
    pub fn move_child(&mut self) {
        if let Some(current) = self.current {
            // We can pop the latest parent node from the guarded nodes.
            self.guarded_nodes.pop();

            self.preceding = Some(Preceding::Parent(current));
            self.current = unsafe { current.as_ref().child };
        }
    }

    /// Moves the cursor through preceding elements until reaching a parent, if no parent is found,
    /// the cursor is reset to its original position.
    ///
    /// Returns `true` if the cursor was moved to a parent, or `false` if not.
    pub fn move_parent(&mut self) -> bool {
        let cache_preceding = self.preceding;
        let cache_current = self.current;
        loop {
            match self.preceding {
                Some(Preceding::Previous(previous)) => {
                    if Some(previous) == *self.root {
                        break;
                    }
                    self.current = Some(previous);
                    self.preceding = unsafe { previous.as_ref().preceding };
                }
                Some(Preceding::Parent(parent)) => {
                    // If we move to a parent node, we add this parent to the guarded nodes to specify that
                    // it cannot be removed (removing it would remove its children which would remove nodes
                    // borrowed by a mutable cursor).
                    self.guarded_nodes.push(parent);

                    self.current = Some(parent);
                    self.preceding = unsafe { parent.as_ref().preceding };
                    return true;
                }
                None => break,
            }
        }
        self.current = cache_current;
        self.preceding = cache_preceding;
        false
    }

    /// Moves the cursor to the successor element if one can be found. If there is no successor
    /// element the cursor is reset to its original position and is not moved.
    ///
    /// Returns `true` if the cursor was moved to a successor, or `false` if not.
    pub fn move_successor(&mut self) -> bool {
        if self.peek_child().is_some() {
            self.move_child();
            true
        } else if self.peek_next().is_some() {
            self.move_next();
            true
        } else {
            // If the element has a parent and the cursor was moved to it.
            if self.move_parent() {
                if self.peek_child().is_some() {
                    self.move_child();
                    true
                } else if self.peek_next().is_some() {
                    self.move_next();
                    true
                } else {
                    false
                }
            } else {
                false
            }
        }
    }

    /// Moves the cursor to the predecessor element if one can be found. If there is no predecessor
    /// element the cursor is reset to its original position and is not moved.
    ///
    /// Returns `true` if the cursor was moved to a predecessor, or `false` if not.
    pub fn move_predecessor(&mut self) -> bool {
        match self.peek_preceding() {
            Some(Preceding::Parent(_)) => {
                self.move_preceding();
                true
            }
            Some(Preceding::Previous(_)) => {
                self.move_preceding();

                loop {
                    if self.peek_child().is_some() {
                        self.move_child();
                        while self.peek_next().is_some() {
                            self.move_next();
                        }
                    } else {
                        break;
                    }
                }

                true
            }
            None => false,
        }
    }

    /// Returns a reference to the next element.
    #[must_use]
    pub fn peek_next(&self) -> Option<&T> {
        if let Some(current) = self.current {
            // We cannot obtain a reference to the next node after the first guarded node as this
            // would be a reference to a node which a mutable cursor could have a mutable reference
            // to (and thus could remove invalidating our reference here).
            if Some(current) == self.guarded_nodes.first().copied() {
                return None;
            }

            unsafe { current.as_ref().next.map(|n| &n.as_ref().element) }
        } else {
            None
        }
    }

    /// Returns a reference to the parent element.
    ///
    /// Wrapper around `self.peek_preceding().and_then(Preceding::parent)`.
    #[must_use]
    pub fn peek_parent(&self) -> Option<&T> {
        self.peek_preceding().and_then(Preceding::parent)
    }

    /// Returns a reference to the previous element.
    ///
    /// Wrapper around `self.peek_preceding().and_then(Preceding::previous)`
    /// .
    #[must_use]
    pub fn peek_previous(&self) -> Option<&T> {
        self.peek_preceding().and_then(Preceding::previous)
    }

    /// Returns a reference to the preceding element.
    #[must_use]
    pub fn peek_preceding(&self) -> Option<Preceding<&T>> {
        self.preceding
            .map(|p| unsafe { p.map(|p| &p.as_ref().element) })
    }

    /// Returns a reference to the child element.
    #[must_use]
    pub fn peek_child(&self) -> Option<&T> {
        if let Some(current) = self.current {
            // We cannot obtain a reference to the next node after the first guarded node as this
            // would be a reference to a node which a mutable cursor could have a mutable reference
            // to (and thus could remove invalidating our reference here).
            if Some(current) == self.guarded_nodes.first().copied() {
                return None;
            }

            unsafe { current.as_ref().child.map(|n| &n.as_ref().element) }
        } else {
            None
        }
    }

    /// Get the current element.
    pub fn current_mut(&self) -> Option<&mut T> {
        self.current
            .map(|mut ptr| unsafe { &mut ptr.as_mut().element })
    }

    /// Removes the current node.
    ///
    /// When removing a node with a child node, this child node is removed.
    pub fn remove_current(&mut self) {
        // We cannot remove the last guarded node, as this node is the n'th parent of the 1st
        // guarded node which is the preceding node of the root node of a mutable cursor. In this
        // case removing this node would deallocate nodes borrowed by the mutable cursor.
        if self.current == self.guarded_nodes.last().copied() {
            return;
        }

        match (self.current, self.preceding) {
            (Some(current), Some(preceding)) => unsafe {
                self.current = current.as_ref().next;
                match preceding {
                    Preceding::Parent(mut parent) => {
                        parent.as_mut().child = current.as_ref().next;
                    }
                    Preceding::Previous(mut previous) => {
                        previous.as_mut().next = current.as_ref().next;
                    }
                }
                if let Some(mut next) = current.as_ref().next {
                    next.as_mut().preceding = Some(preceding);
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
                *self.root = current.as_ref().next;
                if let Some(mut next) = current.as_ref().next {
                    next.as_mut().preceding = None;
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
}

/// Roughly matches [`std::collections::linked_list::Cursor`].
#[derive(Debug)]
pub struct Cursor<'a, T> {
    /// The preceding element, mutably accessing this is unsafe.
    pub preceding: Option<NodePredecessor<T>>,
    /// The current element, mutably accessing this is unsafe.
    pub current: OptionalNode<T>,
    /// The current root element, mutably accessing this is unsafe.
    pub root: &'a OptionalNode<T>,
    /// `self.current` can be equal to `self.succeeding_bound` but it cannot be moved after this,
    /// `self.preceding` cannot be equal to `self.succeeding_bound`.
    pub succeeding_bound: OptionalNode<T>,
}
impl<'a, T> Clone for Cursor<'a, T> {
    fn clone(&self) -> Self {
        Self {
            preceding: self.preceding,
            current: self.current,
            root: self.root,
            succeeding_bound: self.succeeding_bound,
        }
    }
}
impl<'a, T> Cursor<'a, T> {
    /// Get the current element.
    ///
    /// Returns `None` if the current element is `None` or if the current element is the lower bound.
    #[must_use]
    pub fn current(&self) -> Option<&T> {
        self.current.map(|ptr| unsafe { &ptr.as_ref().element })
    }

    /// Moves the cursor to the preceding element.
    ///
    /// If there is no preceding element the cursor is not moved.
    pub fn move_preceding(&mut self) {
        if let Some(preceding) = self.preceding {
            self.current = Some(preceding.unwrap());
            self.preceding = unsafe { preceding.unwrap().as_ref().preceding.as_ref().copied() };
        }
    }

    /// Moves the cursor to the next element if there is some current element and the next element
    /// is within the bounds of the cursor (when splitting a mutable cursor, an immutable cursor is
    /// produced where its bound restrict it to element above the mutable cursor).
    pub fn move_next(&mut self) {
        if let Some(current) = self.current {
            self.preceding = Some(Preceding::Previous(current));
            self.current = unsafe { current.as_ref().next };
        }
    }

    /// Moves the cursor to the child element if there is some current element and the child element
    /// is within the bounds of the cursor (when splitting a mutable cursor, an immutable cursor is
    /// produced where its bound restrict it to element above the mutable cursor).
    pub fn move_child(&mut self) {
        if let Some(current) = self.current {
            self.preceding = Some(Preceding::Parent(current));
            self.current = unsafe { current.as_ref().child };
        }
    }

    /// Moves the cursor through preceding elements until reaching a parent, if no parent is found,
    /// the cursor is reset to its original position.
    ///
    /// Returns `true` if the cursor was moved to a parent, or `false` if not.
    pub fn move_parent(&mut self) -> bool {
        let cache_preceding = self.preceding;
        let cache_current = self.current;
        loop {
            match self.preceding {
                Some(Preceding::Previous(previous)) => {
                    if Some(previous) == *self.root {
                        break;
                    }
                    self.current = Some(previous);
                    self.preceding = unsafe { previous.as_ref().preceding };
                }
                Some(Preceding::Parent(parent)) => {
                    self.current = Some(parent);
                    self.preceding = unsafe { parent.as_ref().preceding };
                    return true;
                }
                None => break,
            }
        }
        self.preceding = cache_preceding;
        self.current = cache_current;
        false
    }

    /// Moves the cursor to the successor element if one can be found. If there is no successor
    /// element the cursor is reset to its original position and is not moved.
    ///
    /// Returns `true` if the cursor was moved to a successor, or `false` if not.
    pub fn move_successor(&mut self) -> bool {
        if self.peek_child().is_some() {
            self.move_child();
            true
        } else if self.peek_next().is_some() {
            self.move_next();
            true
        } else {
            // If the element has a parent and the cursor was moved to it.
            if self.move_parent() {
                if self.peek_child().is_some() {
                    self.move_child();
                    true
                } else if self.peek_next().is_some() {
                    self.move_next();
                    true
                } else {
                    false
                }
            } else {
                false
            }
        }
    }

    /// Moves the cursor to the predecessor element if one can be found. If there is no predecessor
    /// element the cursor is reset to its original position and is not moved.
    ///
    /// Returns `true` if the cursor was moved to a predecessor, or `false` if not.
    pub fn move_predecessor(&mut self) -> bool {
        match self.peek_preceding() {
            Some(Preceding::Parent(_)) => {
                self.move_preceding();
                true
            }
            Some(Preceding::Previous(_)) => {
                self.move_preceding();

                loop {
                    if self.peek_child().is_some() {
                        self.move_child();
                        while self.peek_next().is_some() {
                            self.move_next();
                        }
                    } else {
                        break;
                    }
                }

                true
            }
            None => false,
        }
    }

    /// Returns a reference to the next element.
    #[must_use]
    pub fn peek_next(&self) -> Option<&T> {
        if let Some(current) = self.current {
            // We cannot obtain a reference to the next node after the succeeding bound node as this
            // would be a reference to a node which a mutable cursor could have a mutable reference
            // to (and thus could remove invalidating our reference here).
            if Some(current) == self.succeeding_bound {
                return None;
            }

            unsafe { current.as_ref().next.map(|n| &n.as_ref().element) }
        } else {
            None
        }
    }

    /// Returns a reference to the parent element.
    ///
    /// Wrapper around `self.peek_preceding().and_then(Preceding::parent)`.
    #[must_use]
    pub fn peek_parent(&self) -> Option<&T> {
        self.peek_preceding().and_then(Preceding::parent)
    }

    /// Returns a reference to the previous element.
    ///
    /// Wrapper around `self.peek_preceding().and_then(Preceding::previous)`
    /// .
    #[must_use]
    pub fn peek_previous(&self) -> Option<&T> {
        self.peek_preceding().and_then(Preceding::previous)
    }

    /// Returns a reference to the preceding element.
    #[must_use]
    pub fn peek_preceding(&self) -> Option<Preceding<&T>> {
        self.preceding
            .map(|p| unsafe { p.map(|p| &p.as_ref().element) })
    }

    /// Returns a reference to the child element.
    #[must_use]
    pub fn peek_child(&self) -> Option<&T> {
        if let Some(current) = self.current {
            // We cannot obtain a reference to the next node after the succeeding bound node as this
            // would be a reference to a node which a mutable cursor could have a mutable reference
            // to (and thus could remove invalidating our reference here).
            if Some(current) == self.succeeding_bound {
                return None;
            }

            unsafe { current.as_ref().child.map(|n| &n.as_ref().element) }
        } else {
            None
        }
    }
}

/// Roughly matches [`std::collections::linked_list::CursorMut`].
#[derive(Debug)]
pub struct CursorMut<'a, T> {
    /// The preceding element, mutably accessing this is unsafe.
    pub preceding: Option<NodePredecessor<T>>,
    /// The current element, mutably accessing this is unsafe.
    pub current: OptionalNode<T>,
    /// This can also be a bound where `self.current` can be equal to `self.root` but it cannot be moved before this.
    pub root: &'a mut OptionalNode<T>,
}
impl<'a, T> CursorMut<'a, T> {
    /// Gets a syntax tree where the root is the current node.
    #[must_use]
    pub fn subtree(&self) -> &SyntaxTree<T> {
        unsafe { &*(std::ptr::addr_of!(self.current).cast()) }
    }

    /// Splits the cursor at the current element, where the returned mutable cursor points to the
    /// current element and the return immutable cursor points to the preceding element.
    pub fn split_restricted(&mut self) -> (CursorMut<'_, T>, RestrictedCursor<'_, T>) {
        let cursor = RestrictedCursor {
            preceding: self
                .preceding
                .and_then(|p| unsafe { p.unwrap().as_ref().preceding }),
            current: self.preceding.map(Preceding::unwrap),
            root: self.root,
            guarded_nodes: if let Some(p) = self.preceding.map(Preceding::unwrap) {
                vec![p]
            } else {
                Vec::new()
            },
        };
        let mutable_cursor = CursorMut {
            preceding: self.preceding,
            current: self.current,
            root: &mut self.current,
        };
        (mutable_cursor, cursor)
    }

    /// Splits the tree at the current element.
    pub fn split_next(&mut self) -> OptionalNode<T> {
        match self.current {
            Some(mut current) => unsafe {
                if let Some(next) = current.as_ref().next {
                    current.as_mut().next = None;
                    Some(next)
                } else {
                    None
                }
            },
            None => None,
        }
    }

    /// Splits the cursor at the current element, where the returned mutable cursor points to the
    /// current element and the return immutable cursor points to the preceding element.
    pub fn split(&mut self) -> (CursorMut<'_, T>, Cursor<'_, T>) {
        let cursor = Cursor {
            preceding: self.current.and_then(|c| unsafe { c.as_ref().preceding }),
            current: self.preceding.map(Preceding::unwrap),
            root: self.root,
            succeeding_bound: self.preceding.map(Preceding::unwrap),
        };
        let mutable_cursor = CursorMut {
            preceding: self.preceding,
            current: self.current,
            root: &mut self.current,
        };
        (mutable_cursor, cursor)
    }

    /// Get the current element.
    ///
    /// Returns `None` if the current element is `None` or if the current element is the lower bound.
    #[must_use]
    pub fn current(&self) -> Option<&T> {
        self.current.map(|ptr| unsafe { &ptr.as_ref().element })
    }

    /// Moves the cursor to the preceding element.
    ///
    /// If there is no preceding element or the cursor is at its `preceding_bound` it doesn't move.
    pub fn move_preceding(&mut self) {
        if self.current == *self.root {
            return;
        }
        self.current = self.preceding.map(Preceding::unwrap);
        self.preceding = self
            .preceding
            .and_then(|p| unsafe { p.unwrap().as_ref().preceding });
    }

    /// Moves the cursor to the next element.
    pub fn move_next(&mut self) {
        if let Some(current) = self.current {
            self.preceding = Some(Preceding::Previous(current));
            self.current = unsafe { current.as_ref().next };
        }
    }

    /// Moves the cursor to the child element.
    pub fn move_child(&mut self) {
        if let Some(current) = self.current {
            self.preceding = Some(Preceding::Parent(current));
            self.current = unsafe { current.as_ref().child };
        }
    }

    /// Moves the cursor through preceding elements until reaching a parent, if no parent is found,
    /// the cursor is reset to its original position.
    ///
    /// Returns `true` if the cursor was moved to a parent, or `false` if not.
    pub fn move_parent(&mut self) -> bool {
        let cache_preceding = self.preceding;
        let cache_current = self.current;
        loop {
            match self.preceding {
                Some(Preceding::Previous(previous)) => {
                    if Some(previous) == *self.root {
                        break;
                    }
                    self.current = Some(previous);
                    self.preceding = unsafe { previous.as_ref().preceding };
                }
                Some(Preceding::Parent(parent)) => {
                    self.current = Some(parent);
                    self.preceding = unsafe { parent.as_ref().preceding };
                    return true;
                }
                None => break,
            }
        }
        self.preceding = cache_preceding;
        self.current = cache_current;
        false
    }

    /// Moves the cursor to the successor element if one can be found. If there is no successor
    /// element the cursor is reset to its original position and is not moved.
    ///
    /// Returns `true` if the cursor was moved to a successor, or `false` if not.
    pub fn move_successor(&mut self) -> bool {
        if self.peek_child().is_some() {
            self.move_child();
            true
        } else if self.peek_next().is_some() {
            self.move_next();
            true
        } else {
            // If the element has a parent and the cursor was moved to it.
            if self.move_parent() {
                if self.peek_child().is_some() {
                    self.move_child();
                    true
                } else if self.peek_next().is_some() {
                    self.move_next();
                    true
                } else {
                    false
                }
            } else {
                false
            }
        }
    }

    /// Moves the cursor to the predecessor element if one can be found. If there is no predecessor
    /// element the cursor is reset to its original position and is not moved.
    ///
    /// Returns `true` if the cursor was moved to a predecessor, or `false` if not.
    pub fn move_predecessor(&mut self) -> bool {
        match self.peek_preceding() {
            Some(Preceding::Parent(_)) => {
                self.move_preceding();
                true
            }
            Some(Preceding::Previous(_)) => {
                self.move_preceding();

                loop {
                    if self.peek_child().is_some() {
                        self.move_child();
                        while self.peek_next().is_some() {
                            self.move_next();
                        }
                    } else {
                        break;
                    }
                }

                true
            }
            None => false,
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

    /// Returns a reference to the parent element.
    ///
    /// Wrapper around `self.peek_preceding().and_then(Preceding::parent)`.
    #[must_use]
    pub fn peek_parent(&self) -> Option<&T> {
        self.peek_preceding().and_then(Preceding::parent)
    }

    /// Returns a reference to the previous element.
    ///
    /// Wrapper around `self.peek_preceding().and_then(Preceding::previous)`
    /// .
    #[must_use]
    pub fn peek_previous(&self) -> Option<&T> {
        self.peek_preceding().and_then(Preceding::previous)
    }

    /// Returns a reference to the preceding element.
    #[must_use]
    pub fn peek_preceding(&self) -> Option<Preceding<&T>> {
        if *self.root == self.current {
            return None;
        }

        self.preceding
            .map(|p| unsafe { p.map(|p| &p.as_ref().element) })
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

    /// Get the current element.
    pub fn current_mut(&mut self) -> Option<&mut T> {
        self.current
            .map(|mut ptr| unsafe { &mut ptr.as_mut().element })
    }

    /// Inserts an element before the current element.
    ///
    /// If the cursor has `None` current element it is set to the inserted element.
    pub fn insert_preceding(&mut self, item: T) {
        let ptr = unsafe { alloc::alloc(alloc::Layout::new::<Node<T>>()).cast::<Node<T>>() };
        match (self.current, self.preceding) {
            (Some(mut current), Some(previous)) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        preceding: Some(previous),
                        child: None,
                        next: Some(current),
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                match previous {
                    Preceding::Parent(mut parent) => {
                        parent.as_mut().child = Some(ptr);
                    }
                    Preceding::Previous(mut previous) => {
                        previous.as_mut().next = Some(ptr);
                    }
                }
                let pred = Some(Preceding::Previous(ptr));
                current.as_mut().preceding = pred;
                self.preceding = pred;
            },
            (Some(mut current), None) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        preceding: None,
                        child: None,
                        next: Some(current),
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                let pred = Some(Preceding::Previous(ptr));
                current.as_mut().preceding = pred;
                self.preceding = pred;
                *self.root = Some(ptr);
            },
            (None, Some(previous)) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        preceding: Some(previous),
                        child: None,
                        next: None,
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                match previous {
                    Preceding::Parent(mut parent) => {
                        parent.as_mut().child = Some(ptr);
                    }
                    Preceding::Previous(mut previous) => {
                        previous.as_mut().next = Some(ptr);
                    }
                }
                self.current = Some(ptr);
            },
            (None, None) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        preceding: None,
                        child: None,
                        next: None,
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                self.current = Some(ptr);
                *self.root = Some(ptr);
            },
        }
    }

    /// Inserts an element after the current element.
    ///
    /// If the cursor has `None` current element it is set to the inserted element.
    pub fn insert_next(&mut self, item: T) {
        let ptr = unsafe { alloc::alloc(alloc::Layout::new::<Node<T>>()).cast::<Node<T>>() };
        match (self.current, self.preceding) {
            (Some(mut current), _) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        preceding: Some(Preceding::Previous(current)),
                        child: None,
                        next: current.as_ref().next,
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                if let Some(mut next) = current.as_ref().next {
                    next.as_mut().preceding = Some(Preceding::Previous(ptr));
                }
                current.as_mut().next = Some(ptr);
            },
            (None, Some(preceding)) => match preceding {
                Preceding::Parent(mut parent) => unsafe {
                    ptr::write(
                        ptr,
                        Node {
                            element: item,
                            preceding: Some(Preceding::Parent(parent)),
                            child: None,
                            next: None,
                        },
                    );
                    let ptr = NonNull::new(ptr).unwrap_unchecked();
                    parent.as_mut().child = Some(ptr);
                    self.current = Some(ptr);
                },
                Preceding::Previous(mut previous) => unsafe {
                    ptr::write(
                        ptr,
                        Node {
                            element: item,
                            preceding: Some(Preceding::Previous(previous)),
                            child: None,
                            next: None,
                        },
                    );
                    let ptr = NonNull::new(ptr).unwrap_unchecked();
                    previous.as_mut().next = Some(ptr);
                    self.current = Some(ptr);
                },
            },
            (None, None) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        preceding: None,
                        child: None,
                        next: None,
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                self.current = Some(ptr);
                *self.root = Some(ptr);
            },
        }
    }

    /// Inserts an element as a child of the current element.
    ///
    /// If the cursor has `None` current element it is set to the inserted element.
    pub fn insert_child(&mut self, item: T) {
        let ptr = unsafe { alloc::alloc(alloc::Layout::new::<Node<T>>()).cast::<Node<T>>() };
        match (self.current, self.preceding) {
            (Some(mut current), _) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        preceding: Some(Preceding::Parent(current)),
                        child: None,
                        next: current.as_ref().next,
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                if let Some(mut child) = current.as_ref().child {
                    child.as_mut().preceding = Some(Preceding::Previous(ptr));
                }
                current.as_mut().child = Some(ptr);
            },
            (None, Some(preceding)) => match preceding {
                Preceding::Parent(mut parent) => unsafe {
                    ptr::write(
                        ptr,
                        Node {
                            element: item,
                            preceding: Some(Preceding::Parent(parent)),
                            child: None,
                            next: None,
                        },
                    );
                    let ptr = NonNull::new(ptr).unwrap_unchecked();
                    parent.as_mut().child = Some(ptr);
                    self.current = Some(ptr);
                },
                Preceding::Previous(mut previous) => unsafe {
                    ptr::write(
                        ptr,
                        Node {
                            element: item,
                            preceding: Some(Preceding::Previous(previous)),
                            child: None,
                            next: None,
                        },
                    );
                    let ptr = NonNull::new(ptr).unwrap_unchecked();
                    previous.as_mut().next = Some(ptr);
                    self.current = Some(ptr);
                },
            },
            (None, None) => unsafe {
                ptr::write(
                    ptr,
                    Node {
                        element: item,
                        preceding: None,
                        child: None,
                        next: None,
                    },
                );
                let ptr = NonNull::new(ptr).unwrap_unchecked();
                self.current = Some(ptr);
                *self.root = Some(ptr);
            },
        }
    }

    /// Removes the current node.
    ///
    /// When removing a node with a child node, this child node is removed.
    pub fn remove_current(&mut self) {
        match (self.current, self.preceding) {
            (Some(current), Some(preceding)) => unsafe {
                self.current = current.as_ref().next;
                match preceding {
                    Preceding::Parent(mut parent) => {
                        parent.as_mut().child = current.as_ref().next;
                    }
                    Preceding::Previous(mut previous) => {
                        previous.as_mut().next = current.as_ref().next;
                    }
                }
                if let Some(mut next) = current.as_ref().next {
                    next.as_mut().preceding = Some(preceding);
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
                *self.root = current.as_ref().next;
                if let Some(mut next) = current.as_ref().next {
                    next.as_mut().preceding = None;
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

    /// Moves the children of the current element to next elements.
    pub fn flatten(&self) {
        unsafe {
            if let Some(mut current) = self.current {
                if let Some(mut child) = current.as_ref().child {
                    let mut last_child = child;
                    while let Some(next_child) = last_child.as_ref().next {
                        last_child = next_child;
                    }
                    if let Some(mut next) = current.as_mut().next {
                        next.as_mut().preceding = Some(Preceding::Previous(last_child));
                        last_child.as_mut().next = Some(next);
                    }
                    current.as_mut().next = Some(child);
                    child.as_mut().preceding = Some(Preceding::Previous(current));
                    current.as_mut().child = None;
                }
            }
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
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Preceding<T> {
    /// A parent element.
    Parent(T),
    /// A previous element.
    Previous(T),
}
#[allow(dead_code)]
impl<T> Preceding<T> {
    /// Returns if self is a parent.
    pub fn is_parent(&self) -> bool {
        match self {
            Self::Parent(_) => true,
            Self::Previous(_) => false,
        }
    }
    /// Returns if self is a previous.
    pub fn is_previous(&self) -> bool {
        match self {
            Self::Parent(_) => false,
            Self::Previous(_) => true,
        }
    }
    /// Unwrap to a parent.
    pub fn parent(self) -> Option<T> {
        match self {
            Self::Parent(x) => Some(x),
            Self::Previous(_) => None,
        }
    }
    /// Unwraps to a previous.
    pub fn previous(self) -> Option<T> {
        match self {
            Self::Parent(_) => None,
            Self::Previous(x) => Some(x),
        }
    }
    /// Unwraps.
    pub fn unwrap(self) -> T {
        match self {
            Self::Previous(x) | Self::Parent(x) => x,
        }
    }
    /// Returns `Preceding<&T>`.
    pub fn as_ref(&self) -> Preceding<&T> {
        match self {
            Self::Parent(x) => Preceding::Parent(x),
            Self::Previous(x) => Preceding::Previous(x),
        }
    }
    /// Returns `Preceding<&mut T>`.
    pub fn as_mut(&mut self) -> Preceding<&mut T> {
        match self {
            Self::Parent(x) => Preceding::Parent(x),
            Self::Previous(x) => Preceding::Previous(x),
        }
    }
    /// Maps to `Preceding<P>`.
    pub fn map<P>(self, f: impl Fn(T) -> P) -> Preceding<P> {
        match self {
            Self::Previous(x) => Preceding::Previous(f(x)),
            Self::Parent(x) => Preceding::Parent(f(x)),
        }
    }
}

/// A tree node.
#[derive(Debug)]
pub struct Node<T> {
    /// The element.
    pub element: T,
    /// The preceding node.
    pub preceding: Option<NodePredecessor<T>>,
    /// The child node.
    pub child: Option<NonNull<Node<T>>>,
    /// The next node.
    pub next: Option<NonNull<Node<T>>>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display() {
        let mut tree = SyntaxTree::<u8>::default();
        let mut cursor = tree.cursor_mut();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_child(), None);

        cursor.insert_next(0);
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&0));
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_child(), None);

        cursor.insert_child(1);
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&0));
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_child(), Some(&1));

        cursor.move_child();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Parent(&0)));
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_child(), None);

        cursor.insert_next(2);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Parent(&0)));
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&2));
        assert_eq!(cursor.peek_child(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_child(), None);

        cursor.insert_child(3);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_child(), Some(&3));

        cursor.move_parent();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&0));
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_child(), Some(&1));

        cursor.insert_next(4);
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&0));
        assert_eq!(cursor.peek_next(), Some(&4));
        assert_eq!(cursor.peek_child(), Some(&1));

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&0)));
        assert_eq!(cursor.current(), Some(&4));
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_child(), None);

        cursor.insert_child(5);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&0)));
        assert_eq!(cursor.current(), Some(&4));
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_child(), Some(&5));

        cursor.move_child();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Parent(&4)));
        assert_eq!(cursor.current(), Some(&5));
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_child(), None);

        cursor.insert_next(6);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Parent(&4)));
        assert_eq!(cursor.current(), Some(&5));
        assert_eq!(cursor.peek_next(), Some(&6));
        assert_eq!(cursor.peek_child(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&5)));
        assert_eq!(cursor.current(), Some(&6));
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_child(), None);

        cursor.insert_child(7);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&5)));
        assert_eq!(cursor.current(), Some(&6));
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_child(), Some(&7));

        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some(Element { item: &0, depth: 0 }));
        assert_eq!(iter.next(), Some(Element { item: &1, depth: 1 }));
        assert_eq!(iter.next(), Some(Element { item: &2, depth: 1 }));
        assert_eq!(iter.next(), Some(Element { item: &3, depth: 2 }));
        assert_eq!(iter.next(), Some(Element { item: &4, depth: 0 }));
        assert_eq!(iter.next(), Some(Element { item: &5, depth: 1 }));
        assert_eq!(iter.next(), Some(Element { item: &6, depth: 1 }));
        assert_eq!(iter.next(), Some(Element { item: &7, depth: 2 }));

        let expected = format!(
            "\
            0\n\
            {INDENT}1\n\
            {INDENT}2\n\
            {INDENT}{INDENT}3\n\
            4\n\
            {INDENT}5\n\
            {INDENT}6\n\
            {INDENT}{INDENT}7\n\
        "
        );
        assert_eq!(tree.to_string(), expected);
    }

    #[test]
    fn insert_preceding() {
        let mut tree = SyntaxTree::<u8>::default();
        let mut cursor = tree.cursor_mut();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_preceding(1);
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_preceding(2);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&2)));
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&2)));
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), Some(&1));

        cursor.insert_preceding(3);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&3)));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), Some(&1));

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&2)));
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&2)));
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&3)));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), Some(&1));

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));
    }

    #[test]
    fn insert_next() {
        let mut tree = SyntaxTree::<u8>::default();
        let mut cursor = tree.cursor_mut();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_next(1);
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_next(2);
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&2)));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.insert_next(3);
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&3));

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&3)));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&2)));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&2)));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&3)));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&3));

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&3));
    }

    #[test]
    fn remove() {
        let mut tree = SyntaxTree::<u8>::default();
        let mut cursor = tree.cursor_mut();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_next(1);
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_next(2);
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.insert_next(3);
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&3));

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&3)));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_preceding();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&3));

        cursor.remove_current();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.remove_current();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);
    }

    #[test]
    fn clone() {
        let mut tree = SyntaxTree::<u8>::default();
        let mut cursor = tree.cursor_mut();
        cursor.insert_next(1);
        cursor.insert_preceding(2);
        cursor.insert_next(3);
        cursor.insert_preceding(4);
        cursor.insert_next(5);

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

        tree.cursor_mut().insert_next(1);
        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some(Element { item: &1, depth: 0 }));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(tree.len(), 1);

        tree.cursor_mut().insert_preceding(2);
        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some(Element { item: &2, depth: 0 }));
        assert_eq!(iter.next(), Some(Element { item: &1, depth: 0 }));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(tree.len(), 2);

        tree.cursor_mut().insert_next(3);
        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some(Element { item: &2, depth: 0 }));
        assert_eq!(iter.next(), Some(Element { item: &3, depth: 0 }));
        assert_eq!(iter.next(), Some(Element { item: &1, depth: 0 }));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(tree.len(), 3);

        tree.cursor_mut().insert_preceding(4);
        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some(Element { item: &4, depth: 0 }));
        assert_eq!(iter.next(), Some(Element { item: &2, depth: 0 }));
        assert_eq!(iter.next(), Some(Element { item: &3, depth: 0 }));
        assert_eq!(iter.next(), Some(Element { item: &1, depth: 0 }));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(tree.len(), 4);

        tree.cursor_mut().insert_next(5);
        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some(Element { item: &4, depth: 0 }));
        assert_eq!(iter.next(), Some(Element { item: &5, depth: 0 }));
        assert_eq!(iter.next(), Some(Element { item: &2, depth: 0 }));
        assert_eq!(iter.next(), Some(Element { item: &3, depth: 0 }));
        assert_eq!(iter.next(), Some(Element { item: &1, depth: 0 }));
        assert_eq!(iter.next(), None);
        assert_eq!(tree.len(), 5);
    }

    #[test]
    fn move_parent() {
        let mut tree_one = SyntaxTree::<u8>::default();
        let mut cursor = tree_one.cursor_mut();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_next(1);
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_next(2);
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&2));

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_next(3);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&1)));
        assert_eq!(cursor.current(), Some(&2));
        assert_eq!(cursor.peek_next(), Some(&3));

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&2)));
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_child();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Parent(&3)));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_next(4);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Parent(&3)));
        assert_eq!(cursor.current(), Some(&4));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&4)));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_next(5);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&4)));
        assert_eq!(cursor.current(), Some(&5));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_next();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&5)));
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), None);

        cursor.insert_next(6);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&5)));
        assert_eq!(cursor.current(), Some(&6));
        assert_eq!(cursor.peek_next(), None);

        assert_eq!(cursor.move_parent(), true);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&2)));
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), None);

        assert_eq!(cursor.move_parent(), false);
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&2)));
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), None);
    }
}
