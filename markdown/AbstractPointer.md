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

To abstract over pointer types, we use `impl Deref` in the return types of `left()` and `right()`.
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
to abstract over containers of types. In Rust we can simulate
higher kinded types with GATs.

```rust
trait Ptr {
    type T<'a, U: 'a>: Deref<Target = U>;
}
```

```rust
struct Node<'a, T: 'a, P: Ptr + 'a> {
    data: T,
    left: Option<P::T<'a, Node<'a, T, P>>>,
    right: Option<P::T<'a, Node<'a, T, P>>>,
}
```
