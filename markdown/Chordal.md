Gotchas with chordal register allocation:

* implement_phi_copies has to make a permutation
* permutation != parallel copy, can have multiple duplicate destinations

* enforce_constraints has to shuffle registers to fit the register constraints
in an instruction
  - look at all live variables and determine if they are live through
  at the instruction
  - a live through virtual register could occupy a physical register
  that will be clobbered, those have to be moved into a non-clobbered
  register first
  - construct a bipartite matching problem so that every register
  can be moved into a proper location
  - remember that enforce_constraint only adds extra permutations
  in front of the parallel copy/constrained instruction.
  that instruction still exists and is used
  for *copies*. the (destination, source) pairs created by the bipartite
  matching is for *moves*.
  - bipartite matching problem solved with hungarian
  algorithm
* because of register shuffles from enforcing constraints and optimistic moves, a virtual register
can occupy *multiple* physical registers over its lifetime.
  - for immutable CFGs, can use substitution maps to preserve SSA form, for mutable CFGs can walk def-use
  links and rewrite all uses in blocks that dominate
  the block where the modification happens
  - for immutable CFGs the substitution map method isn't worth it, the mutable CFG method is essentially
  the same as modifying the register in place since you still have to merge a value occupying different registers at join points.
* this means that a virtual register can go in one branch, mutate its physical register and it will have diverging physical registers with the other branch.
and they can join together by having edges to the same successor block.
* when starting coloring a block, look at live vales in predecessors and if their registers differ, *create phi nodes on the fly*.
* blocks are not walked in execution order so when
coloring blocks, `occupied`, `reg_current_var`, and `reg_current_pref` have to be saved and reloaded.