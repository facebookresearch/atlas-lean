# Every constant advice class is strictly contained in P/poly

For every constant $c\ge 0$, $\mathsf{P}/c\subsetneq\mathsf{P}/\mathsf{poly}$; in particular $\mathsf{P}/1\subsetneq\mathsf{P}/\mathsf{poly}$. More generally, for every polynomially bounded advice length $a(n)$ with $a(n)<2^n$ there is a language in $\mathsf{P}/(a(n)+1)$ that is not in $\mathsf{P}/a(n)$.

## Proof sketch

Diagonalize against the countably many clocked polynomial-time machines, assigning each machine its own length $n$: the $a(n)+1$ advice bits at length $n$ give the slice on the first $a(n)+1$ inputs (and the slice is $0$ elsewhere), which a polynomial-time machine reads off its advice; a fixed machine with its $2^{a(n)}$ advice strings of length $a(n)$ realizes at most $2^{a(n)}$ of the $2^{a(n)+1}$ such slices, so one unrealized slice defeats it at its length.

## Depends on

- [Polynomial time with exact-length advice](../../../../complexity-classes/structural-complexity/advice-sparse-and-selective-sets/exact-length-advice-classes.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
