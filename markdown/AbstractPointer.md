# Abstracting over pointer types in C++ and Rust

Pointers have a very general interface. You can get a pointer
to something by taking its address, and you can dereference a pointer to access the data at the address. Pointers don't
specify whether the underlying data came from the stack or the
heap, whether the data was allocated in an arena allocator or a general free-list allocator, or whether the pointer should be freed or not. For example, here's a tree data structure in C:

```c
typedef struct node node;
struct node {
    int32_t data;
    node *left;
    node *right;
};
```

From this type definition, it isn't clear if a `node` is responsible for cleaning up its left and right pointers before being deallocated (aka `node` _owns_ its left and right pointers), or if the left and right pointers will be deallocated separately. We can look for a free function for `node`:

```c
void node_free(node *node)
{
    if (node->left) {
        node_free(node->left);
    }
    if (node->right) {
        node_free(node->right);
    }
    free(node);
}
```

This looks like `node` owns its left and right pointers... as long as the `node_free` function is called on a `node`. In C you can simply not call a free function for a type
and that could mean that a `node` is not intended to own its left and right pointers. Or it could be a mistake and result in a memory leak. You will have to carefully read both the code
that uses a `node` and the various helper functions for `node` to get a full understanding of
what is happening.

C++ and Rust attempt to make this process easier
by having special types for owned pointers. In C++,
the example can be written as:

```cpp
struct Node {
  int32_t data;
  std::unique_ptr<Node> left;
  std::unique_ptr<Node> right;
};
```

`std::unique_ptr` is a container that automatically
deallocates its contained data when its destructor is called. Having `left` and `right` as `std::unique_ptr`s
makes it explicit that `Node` will always own its left
and right pointers.

However encoding ownership and other low-level details in the
type system has a cost. In C, you can write a function that takes in nodes and the function will work with all nodes
regardless of ownership.

```c
void print_node(const node *node)
{
    if (node == NULL) {
        return;
    }
    printf("%d\n", node->data);
    print_node(node->left);
    print_node(node->right);
}
```

```c
// Individual allocations through malloc
{
    node *root = node_alloc(1);
    node *left = node_alloc(2);
    node *right = node_alloc(3);
    assert(root && left && right && "allocation failed");
    root->left = left;
    root->right = right;
    print_node(root);
    node_free(root);
}

// Stack allocation
{
    node nodes[] = {{.data = 1}, {.data = 2}, {.data = 3}};
    nodes[0].left = &nodes[1];
    nodes[0].right = &nodes[2];
    print_node(&nodes[0]);
}

// Arena allocation
{
    arena r = arena_get();
    node *root = arena_alloc(&r, sizeof(node), _Alignof(node), 1);
    node *left = arena_alloc(&r, sizeof(node), _Alignof(node), 1);
    node *right = arena_alloc(&r, sizeof(node), _Alignof(node), 1);
    assert(root && left && right && "allocation failed");
    *root = (node){.data = 1, .left = left, .right = right};
    *left = (node){.data = 2};
    *right = (node){.data = 3};
    print_node(root);
}
```

Whereas functions that take in nodes using owned container types
won't work with other types. Because C++ and Rust heavily favor
using owned types, its easy to start off with them but when you want
to switch to an arena allocator, its difficult to refactor all the
types to a non owned type. And if you want a function to work with
multiple pointer types for things like benchmarking, you will have to
manually duplicate the function for each type.

C++ and Rust will have to leverage their type
systems to be generic over various smart pointer types as
well as raw pointers. Starting with C++, a
single template parameter can be used to generically print any type with a
printable `data` field and
`left` and `right` fields that dereference to the same
type as `node`:

```cpp
template <typename Node> void printNode(const Node &node) {
  std::cout << node.data << "\n";
  if (node.left) {
    printNode(*node.left);
  }
  if (node.right) {
    printNode(*node.right);
  }
}
```

```cpp
struct Node {
  int32_t data;
  std::unique_ptr<Node> left;
  std::unique_ptr<Node> right;
};

struct Node2 {
  int32_t data;
  Node2 *left;
  Node2 *right;
};

int main() {
  auto n1 = std::make_unique<Node>(
      Node{1, std::make_unique<Node>(Node{2, nullptr, nullptr}),
           std::make_unique<Node>(Node{3, nullptr, nullptr})});
  printNode(*n1);

  Node2 left{2, nullptr, nullptr};
  Node2 right{3, nullptr, nullptr};
  Node2 n2{1, &left, &right};
  printNode(n2);
}
```

To prevent duplicating the `Node` struct,
a template can be used to abstract over the pointer type
in the struct definition:

```cpp
template <typename T> using raw_ptr = T *;

template <template <class> class Ptr = std::unique_ptr> struct Node {
  int32_t data;
  Ptr<Node<Ptr>> left;
  Ptr<Node<Ptr>> right;
};

int main() {
  auto n1 = std::make_unique<Node<>>(
      Node<>{1, std::make_unique<Node<>>(Node<>{2, nullptr, nullptr}),
             std::make_unique<Node<>>(Node<>{3, nullptr, nullptr})});
  printNode(*n1);

  Node<raw_ptr> left{2, nullptr, nullptr};
  Node<raw_ptr> right{3, nullptr, nullptr};
  Node<raw_ptr> n2{1, &left, &right};
  printNode(n2);
}
```

Finally, we don't have to hardcode the node's data as a `int32_t`, that
was only to make the C declaration simpler. In C++, it can be generic with another
template parameter:

```cpp
template <typename T, template <class> class Ptr = std::unique_ptr>
struct Node {
  T data;
  Ptr<Node<T, Ptr>> left;
  Ptr<Node<T, Ptr>> right;
};

int main() {
  auto n1 = std::make_unique<Node<int32_t>>(Node<int32_t>{
      1, std::make_unique<Node<int32_t>>(Node<int32_t>{2, nullptr, nullptr}),
      std::make_unique<Node<int32_t>>(Node<int32_t>{3, nullptr, nullptr})});
  printNode(*n1);

  Node<int32_t, raw_ptr> left{2, nullptr, nullptr};
  Node<int32_t, raw_ptr> right{3, nullptr, nullptr};
  Node<int32_t, raw_ptr> n2{1, &left, &right};
  printNode(n2);
}
```

In Rust, abstracting over nodes isn't so simple. C++ templates essentially copy and paste
the specialized type where the template is in the function and check if the result compiles.
In Rust, you have to specify the behavior that you want to abstract over using a trait. For
our example, we want trait methods for getting the left, right, and data fields of the type
implementing our trait:

```rust
trait NodeOps<T> {
    fn data(&self) -> &T;
    fn left(&self) -> &Option<impl Deref<Target = Self>>;
    fn right(&self) -> &Option<impl Deref<Target = Self>>;
}
```

To abstract over pointer-like types, we use `impl Deref` in the return types of `left()` and `right()`.
That will work with `Box`, `Rc`, `bumpalo::boxed::Box`, `&'a T`, etc.

Now that we have our node trait, we can write our function:

```rust
fn print_node<T: Debug, Node: NodeOps<T>>(node: &Node) {
    println!("{:?}", node.data());
    if let Some(left) = node.left() {
        print_node(left.deref());
    }
    if let Some(right) = node.right() {
        print_node(right.deref());
    }
}
```

And for each node type, if we implement `NodeOps` we can use `print_node` with them.

```rust
struct Node<T> {
    data: T,
    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
}

impl<T> NodeOps<T> for Node<T> {
    fn data(&self) -> &T {
        &self.data
    }

    fn left(&self) -> &Option<impl Deref<Target = Self>> {
        &self.left
    }

    fn right(&self) -> &Option<impl Deref<Target = Self>> {
        &self.right
    }
}

struct Node2<'a, T> {
    data: T,
    left: Option<&'a Node2<'a, T>>,
    right: Option<&'a Node2<'a, T>>,
}

impl<'a, T> NodeOps<T> for Node2<'a, T> {
    fn data(&self) -> &T {
        &self.data
    }

    fn left(&self) -> &Option<impl Deref<Target = Self>> {
        &self.left
    }

    fn right(&self) -> &Option<impl Deref<Target = Self>> {
        &self.right
    }
}
```

But what if we don't want to duplicate the node type for each
pointer type? In C++ we used `template<class> class`
for template parameters that themselves take in a template parameter.
How do we do this in Rust?

In other languages like Haskell, higher kinded types are used
to abstract over containers of types.

```haskell
data Node a f = Node
    { nodeData  :: a
    , nodeLeft  :: Maybe (f (Node a f))
    , nodeRight :: Maybe (f (Node a f))
    }
```

In this Haskell code `f` is a type of kind `Type -> Type` compared to
`a` which has kind `Type`, so we can pass types that take types
as parameters like `Maybe` and `Either ()` instead of `Int` and
`String`.

In Rust we can simulate
higher kinded types with generic associated types, which
are associated types that take in type
parameters. Unlike higher kinded types, generic associated
types are attached to a trait, so instead of passing in a type directly
like `Option`, you would have to create a new type and then implement the trait for the type
with its associated type set to `Option<T>`. This is more cumbersome, but
since Rust doesn't have proper higher kinded types, this is the best we can do.

Our pointer trait that contains `T` which is the
generic associated type that stands for any dereferenceable pointer-like type like
`Box`, `bumpalo::boxed::Box`, `&'a T`, etc. is shown below.

```rust
trait Ptr {
    type T<'a, U: 'a>: Deref<Target = U>;
}
```

Because `bumpalo::boxed::Box` and `&'a T` contain a lifetime parameter, the
associated type also has to contain a lifetime parameter `'a` so it
can work with these types and still compile. For other types
like `Box`, the lifetime parameter is ignored.

The associated type has a bound of `Deref` and not `Deref + DerefMut`
because `&'a` doesn't implement `DerefMut`. `T`'s constraints should be
the minimum set of constraints, more can be added later in the where clause of functions if needed.

Now that we have our pointer trait, we can write our generic
`Node` struct:

```rust
struct Node<'a, T: 'a, P: Ptr + 'a> {
    data: T,
    left: Option<P::T<'a, Node<'a, T, P>>>,
    right: Option<P::T<'a, Node<'a, T, P>>>,
}
```

Because `Node` is generic, we no longer need our `NodeOps`
trait and can write the print function directly on `Node`:

```rust
impl<'a, T: Debug, P: Ptr> Node<'a, T, P> {
    fn print(&self) {
        println!("{:?}", self.data);
        if let Some(ref left) = self.left {
            left.print();
        }
        if let Some(ref right) = self.right {
            right.print();
        }
    }
}
```

If you want to write a function that mutates a linked left or right node, `DerefMut`
needs to be added as a constraint to `Ptr::T` in a where clause:

```rust
impl<'a, P: Ptr> Node<'a, i32, P>
where
    P::T<'a, Self>: DerefMut<Target = Self>,
{
    fn incr(&mut self) {
        self.data += 1;
        if let Some(ref mut left) = self.left {
            left.incr();
        }
        if let Some(ref mut right) = self.right {
            right.incr();
        }
    }
}
```

Now in order to use these functions, new types are created
to implement `Ptr` for each type we want to abstract over. Below are the implementations for `Box` and `&'a T`:

```rust
struct BoxPtr;
impl Ptr for BoxPtr {
    type T<'a, U: 'a> = Box<U>;
}

struct RefPtr;
impl Ptr for RefPtr {
    type T<'a, U: 'a> = &'a U;
}

fn main() {
    let mut node: Node<i32, BoxPtr> = Node {
        data: 0,
        left: None,
        right: Some(Box::new(Node {
            data: 1,
            left: None,
            right: None,
        })),
    };
    node.incr(); // incr works with BoxPtr, not RefPtr
    node.print();
    let node: Node<i32, RefPtr> = Node {
        data: 3,
        left: Some(&Node {
            data: 4,
            left: None,
            right: None,
        }),
        right: Some(&Node {
            data: 5,
            left: None,
            right: None,
        }),
    };
    node.print();
}
```

