Stack safe ANF conversion in C++ using Standard ML
==================================================

Recently I've been interested in the idea of writing compilers for
functional programming languages in C++. C++ has the most up-to-date bindings
for generating LLVM IR, and is the most commonly used language for compiler jobs.
So I wanted to get some project experience with C++, and what better way than to
write a small compiler for a functional language in it?

The biggest issue with using C++ for this task is that compilers for functional languages
tend to heavily use recursion for rewriting trees, and with C++ we need to be careful not
to overflow the stack. While with most of the passes I can get by with visitors and explicit
heap allocated stack structures like `std::stack` or `std::vector`, the thing that
stumped me the most was ANF conversion.

What is ANF conversion? Well, one difference between a compiler for a functional language
and an imperative one is that functional compilers have higher order functions which must
be transformed away by the compiler before it can be lowered to LLVM. We also want the compiler to apply specific transformations related to functional programming languages like function uncurrying, argument flattening, etc.

This calls for another intermediate language between the abstract syntax tree and LLVM IR,
which still preserves the tree structure for nested functions, if statements, and join points (which are like basic blocks but with arguments), but otherwise disallows nested expressions. So something that is expressed as `1 + 2 * 3` in the abstract syntax tree
would be represented like:

```
let tmp1 = 2 * 3 in
let tmp2 = 1 + tmp1 in
tmp2
```

This representation is called [A-normal form](https://en.wikipedia.org/wiki/A-normal_form) or ANF for short. ANF conversion is the process of converting the abstract syntax tree into A-normal form. The image below shows the process of ANF conversion for a
expression in a language with if, lambda, apply, and binary operator expressions:

![ANF Conversion Example](anfconvert.png)

How would we implement this transformation? Lets look at a sample example for
if expressions. If we have `1 + if 0 + 1 then 1 + 2 else 2 * 3` what would the output look like?

```
let tmp0 = 0 + 1 in
letjoin tmp1 <tmp2> =
  let tmp3 = 1 + tmp2 in
  tmp3
in
if tmp0 then
  let tmp5 = 1 + 2 in
  jump tmp1 tmp5
else
  let tmp6 = 2 * 3 in
  jump tmp1 tmp6
```

The body of the join point contains the "rest" of the code that uses the value of the if expression (stored in the join point's argument `tmp2`). The
then and else expressions are recursively converted into ANF and linked to a jump expression at the end. The psuedocode for what we want this
transformation to look like is shown below:

```
result_condition = recursively convert condition expression
letjoin joinName <slot>
  [rest of the computation using slot as the value of the if expression]
in
if result_condition then
  result_then = recursively convert then expression
  jump joinName result_then
else
  result_else = recursively convert else expression
  jump joinName result_else
```

Because we have a problem where we want to expand the rest of the computation, we want to pass in a continuation into the conversion
function. The continuation will take as a parameter a value denoting the result of the expression, and return the result of ANF converting the rest of the program. This is what this looks like in C++ (`k` is a member of the `AnfConvertVisitor` class and refers to the continuation):

```cpp
std::unique_ptr<Exp> AnfConvertVisitor::operator()(ast::IfExp &exp) {
  return exp.cond->convert([&thenBranch = *exp.then, &elseBranch = *exp.els,
                            &k = k](Value condValue) {
    auto joinName = fresh();
    auto slot = fresh();
    return make(JoinExp{
        .name = joinName,
        .slot = std::optional{slot},
        .body = k(VarValue{slot}),
        .rest = make(IfExp{
            .cond = condValue,
            .thenBranch = thenBranch.convert([&joinName](Value value) {
              return make(JumpExp{joinName, std::optional{std::move(value)}});
            }),
            .elseBranch = elseBranch.convert([&joinName](Value value) {
              return make(JumpExp{joinName, std::optional{std::move(value)}});
            })})});
  });
}
```

The if else case is the hardest case to handle; the other cases are pretty easy. However, we should take a step back. Just from looking at the if else example it should be clear that the conversion is
happening recursively. We don't want this because if we pass in a larger
AST, then we can get stack overflows.

What we want to do instead is to convert this recursion into a loop. Because
all recursive uses will have to be eliminated, that includes the continuation
call since that is also recursive. This means that the higher order function
`k` will have to be eliminated through the process of defunctionalization.

Because defunctionalization is a pretty involved process, we want to do this
in a language better suited for the task. You could use any functional language with guaranteed tail call elimination like Scheme, Haskell, OCaml, etc. but for this I chose Standard ML because it doesn't have syntax sugar like do notation or let binding syntax, making it slightly easier to identify closures.

Let's start off by writing the basic recursive implementation for ANF
conversion in Standard ML:

```sml
local
  fun go exp k =
    case exp of
      L.Int i => k (Int i)
    | L.Var v => k (Var v)
    | L.Lam (v, body) =>
        let
          val body = go body Halt
          val f = fresh "f"
        in
          Fun (f, [v], body, k (Var f))
        end
    | L.App (f, x) =>
        go f (fn f =>
        go x (fn x =>
        case f of
          Var f => let val r = fresh "r" in App (r, f, [x], k (Var r)) end
        | _ => raise Fail "must apply named value"))
    | L.Bop (bop, x, y) =>
        go x (fn x =>
        go y (fn y =>
        let val r = fresh "r"
        in Bop (r, bop, x, y, k (Var r))
        end))
    | L.If (c, t, f) =>
        go c (fn c =>
          let
            val (j, p) = (fresh "j", fresh "p")
            val jump = fn p => Jump (j, SOME p)
          in
            Join (j, SOME p, k (Var p), If (c, go t jump, go f jump))
          end)
in val convert = fn exp => go exp Halt
end
```

Although we pass in a continuation `k` into the conversion function,
this conversion function is not in continuation passing style form.
In continuation passing style, all function calls are always in
tail position, or in other words, at the very end of the function.
But in this function, we call `k` and use its return value afterwards,
which means it is not called in tail position. So the first thing we need to do
is convert `go` to be in proper continuation passing style form. We do that by
having the continuation `k` itself take in a continuation for what to do
with the result ANF expression. We call this continuation `k'` and it takes
an ANF expression as a parameter and the result. Then, we thread `k'` into
the `go` function as well so that when we need to call `k` we have a `k'` ready
to pass into it.

```sml
local
  fun go (exp: L.exp) (k': exp -> exp) (k: value * (exp -> exp) -> exp) : exp =
    case exp of
      L.Int i => k (Int i, k')
    | L.Var v => k (Var v, k')
    | L.Lam (v, body) =>
        let
          val k' = fn body =>
            let val f = fresh "f"
            in k (Var f, fn rest => k' (Fun (f, [v], body, rest)))
            end
        in
          go body k' (fn (value, k') => k' (Halt value))
        end
    | L.App (f, x) =>
        go f k' (fn (f, k') =>
        go x k' (fn (x, k') =>
        case f of
          Var f =>
            let val r = fresh "r"
            in k (Var r, fn rest => k' (App (r, f, [x], rest)))
            end
        | _ => raise Fail "must apply named value"))
    | L.Bop (bop, x, y) =>
        go x k' (fn (x, k') =>
        go y k' (fn (y, k') =>
        let val r = fresh "r"
        in k (Var r, fn rest => k' (Bop (r, bop, x, y, rest)))
        end))
    | L.If (c, t, f) =>
        go c k' (fn (c, k') =>
          let
            val (j, p) = (fresh "j", fresh "p")
            val jump = fn (v, k') => k' (Jump (j, SOME v))
            val go' = fn e => fn f => go e f jump
          in
            k (Var p, fn rest =>
              go' t (fn t =>
              go' f (fn f =>
              k' (Join (j, SOME p, rest, If (c, t, f))))))
          end)
in
  val convertCPS: L.exp -> exp = fn e =>
    go e (fn a => a) (fn (v, k) => k (Halt v))
end
```

This function is completely tail recursive, but we cannot port this directly to C++ because C++ does not support tail call optimization. Even if
we use Clang and GCC's `musttail` attribute for tail call optimization,
that optimization can only be applied for tail calls with the exact same
type signature as the function itself, which is not the case here. So we still need to do defunctionalization.