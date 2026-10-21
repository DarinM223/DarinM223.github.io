Gotchas when implementing SSA register allocation:
--------------------------------------------------

[SSA register allocation](https://compilers.cs.uni-saarland.de/projects/ssara/) appears to be commonly recommended on places like /r/ProgrammingLanguages, /r/compilers, and Hacker News to people trying to implement register allocation when writing their compilers.
SSA register allocation seems to have a lot of advantages over traditional register allocation strategies. It decouples spilling from register allocation, which results in a cleaner codebase and the ability to use different register allocation algorithms, like preference-based or PBQP, with the same spilling phase. Both spilling and preference-based register allocation can be done with a fixed number of passes, which can potentially result in faster compile times than graph coloring. And the spilling phase is guaranteed to give the minimum spills to lower the maximum register pressure to K registers, instead of linear scan and graph coloring which use heuristics for spilling which can result in unnecessary spills. Both the spilling and the register allocation are performed directly on the SSA form without the need to add another pass to destruct SSA for linear scan or graph coloring (although certain linear scan algorithms can be performed directly on SSA as well). And finally, after skimming the papers for spilling and preference-based register allocation, it seems simple to implement at first glance. However, there are essentially no major compilers that make use of SSA register allocation outside of the reference implementation in the [libfirm](https://github.com/libfirm/libfirm) compiler. If SSA register allocation is so simple and gives so many benefits over existing methods, why haven't more compilers adopted it already?

One reason could be that the paper for preference-based register allocation makes it seem simpler to implement than it actually is. The paper gives pseudocode for the parts of the register allocation that seem to be the most important like the parts around the preference heuristics and how they are used for coloring registers. What's left mostly unmentioned are the parts about enforcing register constraints before an instruction, parts about moving registers to the expected phi registers after a block, and the main coloring function that runs the given function `color_block` for each block in the graph. These parts end up being the most difficult to implement in practice.

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