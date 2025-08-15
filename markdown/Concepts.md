My explanation of the main concepts in Rust
===========================================

There are three main concepts with Rust:

1. Ownership (only one variable "owns" the data at one time, and the owner is in charge of deallocating)
2. Borrowing (you can borrow a reference to an owned variable)
3. Lifetimes (all data keeps track of when it will be destroyed)

These are fairly simple concepts, but they are often counter-intuitive to concepts in other languages, so I wanted to give a shot at
explaining these concepts in more detail. Because Rust is not the only language that uses these concepts
(you can do unique_ptr in C++ for example), learning these concepts will not just help you write better Rust code but better code in general.

Note: I don't cover Rust syntax here so if you cannot understand the syntax try to skim through the short online Rust book first https://doc.rust-lang.org/stable/book/

## Ownership

The concept of ownership is that if you own an item, you are in charge of destroying the item when you are done.

In Rust there can only be **one** owner of a piece of data at any time. This is a lot different from garbage collected languages or languages with raw pointers because instead of having multiple references to the same data, you often have to "juggle" around data so that only one variable owns the data at one time.

Owned data is only automatically deleted when the owned variable no longer holds the data. This can happen when:

1. The owner variable goes out of scope and is destroyed
2. The owner variable is set to another value, making the original data no longer accessable

This simplifies the memory management problem and eliminates the confusing 'which pointer should delete the data at the end?' problem that happens often in C or old C++.
Ownership is not unique to Rust. Modern C++ recommends using 'unique_ptr', a smart pointer that also "owns" the data it wraps, over raw pointers.

When you declare a variable in Rust, the variable "owns" the data.

```rust
let a = Box::new(2); // a "owns" a heap allocated integer
```

When a variable owns something it can move it to other variables using assignment.
After giving away its data, the old variable cannot access the value anymore, and the new variable is the new owner.

```rust
let mufasa = Box::new("king"); // mufasa is the owner of "king"
let scar = mufasa; // the data "king" is moved from mufasa to scar

println!("{}", scar); // scar is now the owner of "king"
println!("{}", mufasa); // ERROR: mufasa can no longer be accessed
```

At the end of the scope where the owner is created, the data is destroyed

```rust
{
	let a = Box::new(2); // a owns a heap allocated integer
} // a's data deallocated here
```

Tips & Tricks:

* Passing values into functions will "move" the data into the function variable. Once that happens the original variable
cannot be accessed. This seems pretty restrictive, which is why the next topic tries to solve this.

```rust
fn hello(a: Box<i32>) {
	println("{:?}", a); // prints "2"
}

fn main() {
	let b = Box::new(2);
	hello(b); // moves b into hello's a parameter

	b; // ERROR: cannot access b after it gave its value to a
}
```

* A common theme when working with Rust is that when data is enclosed by a container like a Vec<Foo> or an Option<Blah>, if you want
to get the data out you have to either manually clone the data or remove it from the container first. One problem is that sometimes you want to move out data out of a container without preventing the container variable from being accessed. To do that, you can use the mem::replace function, which "resets" the variable to a certain value and returns the owned data. Afterwards the original owned variable no longer owns the data and the variable set to the return value now owns the data. For example, here is a code snippet for a linked list:

```rust
use std::mem;

type Link<T> = Option<Box<Node<T>>>;

struct Node<T> {
    data: T,
    next: Link<T>,
}

pub struct Stack<T> {
    size: i32,
    head: Link<T>,
}

impl<T> Stack<T> {
    // ... other methods

    pub fn pop(&mut self) -> Option<T> {
        let head = mem::replace(&mut self.head, None); // retrieve the Node from the Option and and set self.head to be None
        head.map(|old_head| {
            let old_head = *old_head;
            self.head = old_head.next;
            self.size -= 1;

            old_head.data
        })
    }
}
```

Because this case is especially common with Options, there is a take() method for Options that does the same thing but is less verbose:

```rust
impl<T> Stack<T> {
    // ... other methods

    pub fn pop(&mut self) -> Option<T> {
        self.head.take().map(|old_head| { // retrieve the Node from the Option and set self.head to be None
            let old_head = *old_head;
            self.head = old_head.next; // self.head is None so you can freely set it
            self.size -= 1;

            old_head.data
        })
    }
}
```

## Borrowing

The previous section highlighted a big flaw with ownership by itself.
There are many cases where you want to manipulate data, without actually owning the data.
For example you might want to pass a value to a function and still be able to call the owner variable outside the function.

Rust allows you to do this using the concept of borrowing. Borrowing is just like what you think it is, it just allows
another variable to temporarily borrow the data in your variable and gives it back when its done.

Rust allows you to have two types of borrows:

* immutable borrows with '&' (you can read the value of the borrowed data, but you can't modify it)
* mutable borrows with '&mut' (you can both read and modify the value of the borrowed data)

You can either have:

* A lot of immutable borrows
* Only one mutable borrow

in a scope for a piece of data at any given time. So you should try to do immutable borrows most of the time and only do
a mutable borrow when you really need it.

To access the value in a borrowed reference you use the dereference operator '*'.

When you borrow a variable, the owner variable becomes inaccessable until the borrowed variable
is destroyed.

```rust
let mut x = 5;
let y = &mut x; // y borrows the data from x
println!("{}", x); // ERROR: x no longer has the data, y has it!
```

When a borrowed variable is destroyed, it gives back the borrowed value back to the owner.

```rust
let mut x = 5;

{
    let y = &mut x; // y borrows the data from x
    *y += 1; // y changes the borrowed data
} // y gives back the data to x

println!("{}", x); // x has the data back again (and its changed to 6)
```

Because of this, the owner has to live longer than the borrower

```rust
let mut x: &i32;

{
	let y = 3;
	x = &y; // ERROR: x lives longer than y!
} // y gets destroyed here! What would happen to x if the Rust compiler didn't prevent this from happening?
```

Tips & Tricks:

* Function parameters end up mostly being borrowed references because otherwise the value will be moved inside the function
* Function return values should not be references to local variables and Rust will not let you do this.
If you returned a pointer to a local value in C you could either end up with corrupted data or the return value won't know when to deallocate its data
which is bad either way you look at it
* Don't worry about dereferencing to "read" or "write" (depending on & or &mut) the value of a borrowed reference

```rust
enum State {
	Hello,
	Bye,
}
fn hello(blah: &State, foo: &mut i32) {
	match *blah { // you are only reading an immutable reference so its fine
		State::Hello => println!("Hello!"),
		State::Bye => println!("Bye!"),
	}

	*foo += 1; // you are only writing to a mutable reference so its fine
}
```

* Do worry about assigning dereferenced references to variables, because that will instead try to move the data to the new variable

```rust
enum State {
	Hello,
	Bye,
}
fn hello(blah: &State) {
	let thief = *blah; // ERROR: blah can't give a borrowed item to thief!
	                   // thief is going to take the value without giving it back to the original owner
}
```

* Assignment is not the only thing that will attempt to move out of a borrowed reference. For example, pattern matching also tries to move the value.
To prevent this, precede the match variable with 'ref' to borrow the match variable instead of moving

```rust
enum State {
    Hello(String),
    Bye,
}

fn hello(blah: &State) {
    match *blah {
        State::Hello(s) => println!("Hello, {}", s), // ERROR: moves data inside blah (the string) into the variable s
        State::Bye => println!("Bye!"),
    }

    // do this instead
    match *blah {
        State::Hello(ref s) => println!("Hello, {}", s), // borrow the string data inside blah
        State::Bye => println!("Bye!"),
    }
}
```

## Lifetimes

TODO: write this later