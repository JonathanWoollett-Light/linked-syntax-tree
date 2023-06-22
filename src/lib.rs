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

/// A doubly-linked syntax tree.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub struct SyntaxTree<T> {
    root: Option<NonNull<Node<T>>>,
}

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

type NodePredecessor<T> = Preceding<NonNull<Node<T>>>;

impl<T> SyntaxTree<T> {
    /// Provides a cursor at the front element.
    #[must_use]
    pub fn cursor(&self) -> Cursor<T> {
        Cursor {
            preceding: None,
            current: self.root,
            tree: NonNull::new(self as *const _ as *mut _).unwrap(),
            lower_bound: None,
        }
    }

    /// Provides a cursor with editing operation at the root element.
    pub fn cursor_mut(&mut self) -> CursorMut<T> {
        CursorMut {
            preceding: None,
            current: self.root,
            tree: NonNull::new(self).unwrap(),
            upper_bound: None,
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
        let stack = if let Some(root) = self.root {
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
        Self { root: Some(ptr) }
    }
}

/// Iterates through elements depth-first in a [`SyntaxTree`] returning references.
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

/// Iterates through elements depth-first in a [`SyntaxTree`] returning mutable references.
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

/// An element in a [`SyntaxTree`] with a known depth.
#[derive(Debug, Eq, PartialEq)]
pub struct Element<T> {
    /// The data within the node.
    pub item: T,
    /// The depth of the node.
    pub depth: usize,
}

/// Roughly matches [`std::collections::linked_list::Cursor`].
#[derive(Debug)]
pub struct Cursor<T> {
    preceding: Option<NodePredecessor<T>>,
    current: Option<NonNull<Node<T>>>,
    /// The underlying [`SyntaxTree`].
    pub tree: NonNull<SyntaxTree<T>>,
    lower_bound: Option<NonNull<Node<T>>>,
}
impl<T> Clone for Cursor<T> {
    fn clone(&self) -> Self {
        Self {
            preceding: self.preceding,
            current: self.current,
            tree: self.tree,
            lower_bound: self.lower_bound,
        }
    }
}
impl<T> Cursor<T> {
    /// Sets the `preceding` member.
    pub fn set_preceding(&mut self, preceding: Option<NodePredecessor<T>>) {
        self.preceding = preceding;
    }

    /// Sets the `current` member.
    pub fn set_current(&mut self, current: Option<NonNull<Node<T>>>) {
        self.current = current;
    }

    /// Gets the `preceding` member.
    #[must_use]
    pub fn get_preceding(&self) -> &Option<NodePredecessor<T>> {
        &self.preceding
    }

    /// Gets the `current` member.
    #[must_use]
    pub fn get_current(&self) -> &Option<NonNull<Node<T>>> {
        &self.current
    }

    /// Constructs a new cursor.
    ///
    /// # Safety
    ///
    /// Requires that `preceding` and `current` are present nodes in `tree` and that `preceding` is
    /// the preceding node to `current`.
    #[must_use]
    pub unsafe fn new(
        preceding: Option<NodePredecessor<T>>,
        current: Option<NonNull<Node<T>>>,
        tree: NonNull<SyntaxTree<T>>,
        lower_bound: Option<NonNull<Node<T>>>,
    ) -> Cursor<T> {
        Cursor {
            preceding,
            current,
            tree,
            lower_bound,
        }
    }

    /// Provides a reference to the root element.
    #[must_use]
    pub fn root(&self) -> Option<&T> {
        unsafe {
            let mut preceding_opt = self.preceding;
            while let Some(preceding) = preceding_opt {
                preceding_opt = preceding.unwrap().as_ref().preceding;
            }
            preceding_opt.map(|p|&p.unwrap().as_ref().element)
        }
    }

    /// Get the current element.
    ///
    /// Returns `None` if the current element is `None` or if the current element is the lower bound.
    #[must_use]
    pub fn current(&self) -> Option<&T> {
        if self.current == self.lower_bound {
            return None;
        }
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

    /// Moves the cursor to the next element.
    pub fn move_next(&mut self) {
        if let Some(current) = self.current {
            if let Some(guard) = self.lower_bound {
                if guard == current {
                    return;
                }
            }
            self.preceding = Some(Preceding::Previous(current));
            self.current = unsafe { current.as_ref().next };
        }
    }

    /// Moves the cursor to the child element.
    pub fn move_child(&mut self) {
        if let Some(current) = self.current {
            if let Some(guard) = self.lower_bound {
                if guard == current {
                    return;
                }
            }
            self.preceding = Some(Preceding::Parent(current));
            let opt = unsafe { current.as_ref().child.as_ref() };
            self.current = opt.copied();
        }
    }

    /// Moves the cursor through preceding elements until reaching a parent or
    /// the root element.
    ///
    /// Returns `true` if the cursor was moved to a parent or `false` if it was moved to the root
    /// element.
    pub fn move_parent(&mut self) -> bool {
        loop {
            match self.preceding {
                Some(Preceding::Previous(previous)) => {
                    self.current = Some(previous);
                    self.preceding = unsafe { previous.as_ref().preceding };
                }
                Some(Preceding::Parent(parent)) => {
                    self.current = Some(parent);
                    self.preceding = unsafe { parent.as_ref().preceding };
                    break true;
                }
                None => break false,
            }
        }
    }

    /// Moves the cursor to the successor element or the root element if a successor is not present.
    ///
    /// Returns `true` if the cursor was moved to a successor or `false` if it was moved to the root
    /// element.
    pub fn move_successor(&mut self) -> bool {
        if self.peek_child().is_some() {
            self.move_child();
            true
        } else if self.peek_next().is_some() {
            self.move_next();
            true
        } else {
            let parent = self.move_parent();
            let cond = parent && self.peek_next().is_some();
            if cond {
                self.move_next();
            }
            cond
        }
    }

    /// Moves the cursor to the predecessor element or the root element if a predecessor is not
    /// present.
    ///
    /// Returns `true` if the cursor was moved to a predecessor or `false` if it was moved to the
    /// root element.
    pub fn move_predecessor(&mut self) -> bool {
        match self.peek_preceding() {
            Some(Preceding::Parent(_)) => {
                self.move_preceding();
                true
            }
            Some(Preceding::Previous(_)) => {
                self.move_preceding();
                while self.peek_child().is_some() {
                    self.move_child();
                    while self.peek_next().is_some() {
                        self.move_next();
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
            if let Some(guard) = self.lower_bound {
                if guard == current {
                    return None;
                }
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
            if let Some(guard) = self.lower_bound {
                if guard == current {
                    return None;
                }
            }
            unsafe { current.as_ref().child.map(|n| &n.as_ref().element) }
        } else {
            None
        }
    }
}

/// Roughly matches [`std::collections::linked_list::CursorMut`].
#[derive(Debug)]
pub struct CursorMut<T> {
    preceding: Option<NodePredecessor<T>>,
    current: Option<NonNull<Node<T>>>,
    /// The underlying [`SyntaxTree`].
    pub tree: NonNull<SyntaxTree<T>>,
    upper_bound: Option<NodePredecessor<T>>,
}

impl<T> CursorMut<T> {
    /// Sets the `preceding` member.
    pub fn set_preceding(&mut self, preceding: Option<NodePredecessor<T>>) {
        self.preceding = preceding;
    }

    /// Sets the `current` member.
    pub fn set_current(&mut self, current: Option<NonNull<Node<T>>>) {
        self.current = current;
    }

    /// Gets the `preceding` member.
    #[must_use]
    pub fn get_preceding(&self) -> &Option<NodePredecessor<T>> {
        &self.preceding
    }

    /// Gets the `current` member.
    #[must_use]
    pub fn get_current(&self) -> &Option<NonNull<Node<T>>> {
        &self.current
    }

    /// Constructs a new cursor.
    ///
    /// # Safety
    ///
    /// Requires that `preceding` and `current` are present nodes in `tree` and that `preceding` is
    /// the preceding node to `current`.
    #[must_use]
    pub unsafe fn new(
        preceding: Option<NodePredecessor<T>>,
        current: Option<NonNull<Node<T>>>,
        tree: NonNull<SyntaxTree<T>>,
        upper_bound: Option<NodePredecessor<T>>,
    ) -> CursorMut<T> {
        CursorMut {
            preceding,
            current,
            tree,
            upper_bound,
        }
    }

    /// Provides a reference to the root element.
    #[must_use]
    pub fn root(&self) -> Option<&T> {
        unsafe {
            match self.upper_bound {
                Some(Preceding::Parent(parent)) => {
                    parent.as_ref().child.map(|c| &c.as_ref().element)
                }
                Some(Preceding::Previous(previous)) => {
                    previous.as_ref().next.map(|n| &n.as_ref().element)
                }
                None => {
                    let mut preceding_opt = self.preceding;
                    while let Some(preceding) = preceding_opt {
                        preceding_opt = preceding.unwrap().as_ref().preceding;
                    }
                    preceding_opt.map(|p|&p.unwrap().as_ref().element)
                },
            }
        }
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
    /// If there is no preceding element the cursor is not moved.
    pub fn move_preceding(&mut self) {
        // When `self.preceding == None` `self.upper_bound` will be `None`.
        if self.preceding == self.upper_bound {
            return;
        }
        self.current = Some(self.preceding.unwrap().unwrap());
        self.preceding = unsafe {
            self.preceding
                .unwrap()
                .unwrap()
                .as_ref()
                .preceding
                .as_ref()
                .copied()
        };
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
            let opt = unsafe { current.as_ref().child.as_ref() };
            self.current = opt.copied();
        }
    }

    /// Moves the cursor through preceding elements until reaching a parent or
    /// the root element.
    ///
    /// Returns `true` if the cursor was moved to a parent or `false` if it was moved to the root
    /// element.
    pub fn move_parent(&mut self) -> bool {
        loop {
            if self.preceding == self.upper_bound {
                break false;
            }

            match self.preceding {
                Some(Preceding::Previous(previous)) => {
                    self.current = Some(previous);
                    self.preceding = unsafe { previous.as_ref().preceding };
                }
                Some(Preceding::Parent(parent)) => {
                    self.current = Some(parent);
                    self.preceding = unsafe { parent.as_ref().preceding };
                    break true;
                }
                None => break false,
            }
        }
    }

    /// Moves the cursor to the successor element or the root element if a successor is not present.
    ///
    /// Returns `true` if the cursor was moved to a successor or `false` if it was moved to the root
    /// element.
    pub fn move_successor(&mut self) -> bool {
        if self.peek_child().is_some() {
            self.move_child();
            true
        } else if self.peek_next().is_some() {
            self.move_next();
            true
        } else {
            let parent = self.move_parent();
            let cond = parent && self.peek_next().is_some();
            if cond {
                self.move_next();
            }
            cond
        }
    }

    /// Moves the cursor to the predecessor element or the root element if a predecessor is not
    /// present.
    ///
    /// Returns `true` if the cursor was moved to a predecessor or `false` if it was moved to the
    /// root element.
    pub fn move_predecessor(&mut self) -> bool {
        match self.peek_preceding() {
            Some(Preceding::Parent(_)) => {
                self.move_preceding();
                true
            }
            Some(Preceding::Previous(_)) => {
                self.move_preceding();
                while self.peek_child().is_some() {
                    self.move_child();
                    while self.peek_next().is_some() {
                        self.move_next();
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
        if self.upper_bound == self.preceding {
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

    /// Provides a mutable reference to the root element.
    pub fn root_mut(&mut self) -> Option<&mut T> {
        unsafe {
            let mut preceding_opt = self.preceding;
            while let Some(preceding) = preceding_opt {
                preceding_opt = preceding.unwrap().as_ref().preceding;
            }
            preceding_opt.map(|p|&mut p.unwrap().as_mut().element)
        }
    }

    /// Get the current element.
    pub fn current_mut(&mut self) -> Option<&mut T> {
        self.current
            .map(|mut ptr| unsafe { &mut ptr.as_mut().element })
    }

    /// Returns an immutable cursor to all elements before the current element.
    pub fn split(&mut self) -> Cursor<T> {
        self.upper_bound = self.preceding;
        Cursor {
            preceding: self
                .preceding
                .and_then(|p| unsafe { p.unwrap().as_ref().preceding }),
            current: self.preceding.map(Preceding::unwrap),
            tree: self.tree,
            lower_bound: self.current,
        }
    }

    /// Joins an immutable cursor into a mutable cursor.
    pub fn try_join(&mut self, cursor: Cursor<T>) -> Result<(), Cursor<T>> {
        unsafe {
            match self.upper_bound {
                Some(Preceding::Parent(parent)) if parent.as_ref().child == cursor.lower_bound => {
                    self.upper_bound = None;
                    Ok(())
                }
                Some(Preceding::Previous(previous))
                    if previous.as_ref().next == cursor.lower_bound =>
                {
                    self.upper_bound = None;
                    Ok(())
                }
                // TODO Is this correct?
                None => Ok(()),
                _ => Err(cursor),
            }
        }
    }

    // TODO Make `insert_preceding`, `insert_next`, `insert_child`, `flatten` and `remove_current` work with `self.upper_bound`.

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
                self.tree.as_mut().root = Some(ptr);
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
                self.tree.as_mut().root = Some(ptr);
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
                self.tree.as_mut().root = Some(ptr);
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
                self.tree.as_mut().root = Some(ptr);
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
                self.tree.as_mut().root = current.as_ref().next;
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
    pub fn flatten(&mut self) {
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
                }
            }
        }
    }
}

/// A relationship between an element its preceding element.
#[derive(Debug)]
pub enum Relationship {
    /// The preceding element is its previous element.
    Previous,
    /// The preceding element is its parent element.
    Parent,
}
impl Default for Relationship {
    fn default() -> Self {
        Self::Previous
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

/// A [`SyntaxTree`] node.
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

        cursor.move_parent();
        assert_eq!(cursor.peek_preceding(), Some(Preceding::Previous(&2)));
        assert_eq!(cursor.current(), Some(&3));
        assert_eq!(cursor.peek_next(), None);

        cursor.move_parent();
        assert_eq!(cursor.peek_preceding(), None);
        assert_eq!(cursor.current(), Some(&1));
        assert_eq!(cursor.peek_next(), Some(&2));
    }
}
