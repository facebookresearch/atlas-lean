# Optimal shallow circuits for symmetric functions and majority

For every depth $d\ge2$ there is a constant $C$ such that every symmetric Boolean function of $n$ bits (in particular $\mathrm{MAJ}_n$) has alternating formulas of depth $d$ with at most $2^{Cn^{1/(d-1)}}$ gates, and hence circuits over the unbounded fan-in basis of AND/OR depth $d$ with at most $2^{Cn^{1/(d-1)}}+n$ gates. For depth three this is $2^{O(\sqrt n)}$. The exponent $n^{1/(d-1)}$ is optimal for majority by Korten's top-down bound.

## Proof sketch

Reduce the exact-weight test to conjunctions of symmetric two-block comparisons modulo coprime moduli chosen at scale $n^{1/(d-1)}$, covering the cube by few shifted distinctness tests; recursion on depth reduces the block size by the same factor at each level.

## Depends on

- [Alternating formulas of depth d](alternating-formulas-of-depth-d.md)
- [Majority function](../../../Combinatorics/boolean-functions/majority-is-least-stable-conjecture/majority.md)

## Proof depends on

- [Korten's top-down lower bounds for constant depth](korten-top-down-lower-bounds.md)

## Sources

- Victor Lecomte, Prasanna Ramakrishnan, "Optimal Shallow Circuits for Majority", 2026.
