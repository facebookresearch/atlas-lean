# Closure properties of P/poly

$\mathsf{P}/\mathsf{poly}$ is closed under complement, finite union and intersection, polynomial-time many-one reductions, and more generally under reductions computed by polynomial-size circuit families: if $L'\in\mathsf{P}/\mathsf{poly}$ and $x\in L\iff g(x)\in L'$ for a length-regular map $g$ whose slices have polynomial-size circuits, then $L\in\mathsf{P}/\mathsf{poly}$. Moreover $\mathsf{P}\subseteq\mathsf{P}/\mathsf{poly}$.

## Proof sketch

Compose circuits: a circuit for $g$ on length $n$ followed by the circuit for $L'$ at length $|g(x)|$; Boolean operations add a gate.

## Depends on

- [Polynomial time with polynomial advice](../../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Proof depends on

- [P is contained in P/poly](../../../../complexity-classes/time-and-space-complexity-classes/p-is-contained-in-p-poly.md)

## Sources

- Richard M. Karp, Richard J. Lipton, "Some Connections between Nonuniform and Uniform Complexity Classes", Proceedings of the 12th Annual ACM Symposium on Theory of Computing, 1980.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
