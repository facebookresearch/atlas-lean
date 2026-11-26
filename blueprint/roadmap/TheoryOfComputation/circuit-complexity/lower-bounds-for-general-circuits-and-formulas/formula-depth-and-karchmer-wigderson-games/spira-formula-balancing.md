# Spira's theorem: balancing formulas

Every De Morgan formula with $L\ge 1$ leaves has an equivalent De Morgan formula with at most $4\lceil\log_2 L\rceil$ AND and OR gates on every root-to-leaf path. Consequently the formula depth $D(f)$ and formula leaf size $L(f)$ satisfy $\log_2 L(f)\le D(f)\le 4\log_2 L(f)$.

## Proof sketch

Find a subformula $G$ with between $L/3$ and $2L/3$ leaves; write $F=(G\wedge F[G:=1])\vee(\neg G\wedge F[G:=0])$ and balance $G$ and the two restrictions recursively. Each recursion level shrinks the leaf count by a factor $2/3$ and adds a constant number of levels, giving depth $O(\log L)$ with constant $4$.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Formula depth from formula leaf size](../formula-size-lower-bounds/formula-depth-lower-bound-from-leaf-size.md)

## Sources

- Philip M. Spira, "On Time-Hardware Complexity Tradeoffs for Boolean Functions", Proceedings of the Fourth Hawaii International Symposium on System Sciences, 1971.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
