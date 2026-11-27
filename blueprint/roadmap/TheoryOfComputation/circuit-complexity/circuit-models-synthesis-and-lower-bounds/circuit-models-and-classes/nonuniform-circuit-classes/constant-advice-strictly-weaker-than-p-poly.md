# Every constant advice class is strictly contained in P/poly

For every constant $c\ge 0$, $\mathsf{P}/c\subsetneq\mathsf{P}/\mathsf{poly}$; in particular $\mathsf{P}/1\subsetneq\mathsf{P}/\mathsf{poly}$. More generally, for every polynomially bounded advice length $a(n)$ (indeed every $a(n)<2^n$) there is a language in $\mathsf{P}/(a(n)+1)$ that is not in $\mathsf{P}/a(n)$.

## Proof sketch

Diagonalize against the countably many pairs (machine, advice string of length $a(n)$) at each length: the $a(n)+1$ advice bits at length $n$ give the slice on the first $a(n)+1$ inputs; a fixed machine with its $2^{a(n)}$ advice strings realizes at most $2^{a(n)}$ of the $2^{a(n)+1}$ such slices, so one unrealized slice defeats it, and each machine is defeated at infinitely many lengths.

## Depends on

- [Polynomial time with exact-length advice](../../../../complexity-classes/structural-complexity/advice-sparse-and-selective-sets/exact-length-advice-classes.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 3–5", 2007.
