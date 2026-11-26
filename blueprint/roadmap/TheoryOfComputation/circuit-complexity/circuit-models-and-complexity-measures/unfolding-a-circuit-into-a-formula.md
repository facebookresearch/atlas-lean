# Unfolding a circuit into a formula of the same depth

Every circuit over a basis of fan-in at most $r$ of depth $d$ computes the same function as a formula over the same basis of depth $d$ obtained by copying each gate once for every path from it to the output. The formula has at most $r^d$ leaves and fewer than $r^{d+1}$ nodes. Conversely, a formula with at most $d$ AND and OR gates on every path has at most $2^d$ leaves.

## Proof sketch

Induction on depth: the formula of a gate is the gate applied to the formulas of its arguments, and each argument formula has depth one less.

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
