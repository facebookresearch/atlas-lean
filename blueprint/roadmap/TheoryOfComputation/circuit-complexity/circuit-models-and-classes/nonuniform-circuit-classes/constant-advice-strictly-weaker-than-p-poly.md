# Every constant advice class is strictly contained in P/poly

For every constant $c\ge 0$, $\mathsf{P}/c\subsetneq\mathsf{P}/\mathsf{poly}$; in particular $\mathsf{P}/1\subsetneq\mathsf{P}/\mathsf{poly}$. More generally, for every advice length $a(n)$ there is a language in $\mathsf{P}/(a(n)+1)$, with polynomially bounded advice, that is not in $\mathsf{P}/a(n)$.

## Proof sketch

Diagonalize against the countably many pairs (machine, advice string of length $a(n)$) at each length: one extra advice bit at length $n$ can encode the answer that defeats all machine–advice combinations on a designated input, by a counting argument on the number of possible advice strings.

## Depends on

- [Polynomial time with exact-length advice](../../../complexity-classes/structural-complexity/advice-sparse-and-selective-sets/exact-length-advice-classes.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 3–5", 2007.
