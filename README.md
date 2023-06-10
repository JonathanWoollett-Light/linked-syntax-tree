# linked-syntax-tree

A doubly-linked syntax tree.

Offers functionality similar to [`std::collections::LinkedList`](https://doc.rust-lang.org/std/collections/struct.LinkedList.html).

Some code:

```text
x = -10
loop
    x = x + 1
    if x
        break
x = 2
```

can be represented as:

```text
┌──────────┐
│x = -10   │
└──────────┘
│
┌──────────┐
│loop      │
└──────────┘
│           ╲
┌──────────┐ ┌─────────┐
│x = 2     │ │x = x + 1│
└──────────┘ └─────────┘
             │
             ┌─────────┐
             │if x     │
             └─────────┘
                        ╲
                         ┌─────────┐
                         │break    │
                         └─────────┘
```

I personally am using this to contain an AST for compile-time evaluate.
