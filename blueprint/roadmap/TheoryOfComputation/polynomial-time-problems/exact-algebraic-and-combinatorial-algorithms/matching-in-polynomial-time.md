# The parity of the number of perfect matchings of a bipartite graph is polynomial-time computable

The parity of the number of perfect matchings of a bipartite graph equals the determinant of its biadjacency matrix modulo $2$ and is polynomial-time computable on multi-tape Turing machines.

## Proof sketch

The number of perfect matchings is the permanent of the biadjacency matrix, and $\operatorname{perm}\equiv\det\pmod 2$; the integer determinant is computable in polynomial time by fraction-free Gaussian elimination.

## Depends on

- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)
- [The 0-1 permanent counts perfect matchings](../../counting-complexity/complexity-of-the-permanent/permanent-boole-eq-card.md)

## Proof depends on

- [Permanent equals determinant in characteristic two](../../counting-complexity/complexity-of-the-permanent/permanent-eq-det-of-char-p-two.md)
- [Polynomial-time rational Gaussian elimination (Bareiss)](bareiss-rational-gaussian-elimination.md)

## Sources

- Leslie G. Valiant, "The Complexity of Computing the Permanent", Theoretical Computer Science 8(2), 189–201, 1979.
