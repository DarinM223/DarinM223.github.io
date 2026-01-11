Abstracting over pointer types in C++ and Rust
==============================================

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

From this type definition, it isn't clear if a `node` is responsible for cleaning up its left and right pointers before being deallocated (aka `node` *owns* its left and right pointers), or if the left and right pointers will be deallocated separately. We can look for a free function for `node`:

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

This looks like `node` owns its left and right pointers... as long as the `node_free` function is called on a `node`. Unlike in C++ or Rust, in C you can simply not call a free function for a type
and that could mean that a `node` is not intended to own its left and right pointers. Or it could be a mistake and result in a memory leak. You will have to carefully read both the code
that uses a `node` and the various helper functions for `node` to get a full understanding of
what is happening.

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
    node_free(root); // root owns left and right
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