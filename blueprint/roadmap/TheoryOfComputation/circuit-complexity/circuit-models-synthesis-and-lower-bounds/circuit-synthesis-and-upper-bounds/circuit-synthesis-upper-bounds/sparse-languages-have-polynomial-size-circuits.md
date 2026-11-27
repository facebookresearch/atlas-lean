# Sparse languages have polynomial-size circuits

Every sparse language (one with polynomially many words of each length; in particular every unary language $L\subseteq 1^*$) belongs to $\mathsf{P}/\mathsf{poly}$, that is, has polynomial-size circuits.

## Proof sketch

A language $L$ has polynomial-size circuits if and only if $L\in\mathsf{P}^S$ for some sparse set $S$; a sparse $L$ is in $\mathsf{P}^L$ by one oracle query, so it has polynomial-size circuits. Directly, and derived here with explicit constants: if the slice $L\cap\{0,1\}^n$ contains at most $k$ words, it is the disjunction of the minterms of those words; each minterm uses at most $2n$ De Morgan gates (negations included) and the disjunction at most $k$ more, so the slice has a De Morgan circuit with at most $k(2n+2)+1$ gates, which is polynomial in $n$ when $k$ is.

## Depends on

- [Polynomial time with polynomial advice](../../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [Sparse decision problems](../../../../complexity-classes/mahaney-s-theorem/sparse.md)

## Proof depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- Jin-Yi Cai, "Lectures in Computational Complexity", lecture notes, University of Wisconsin–Madison, 2003 (Section 4.1, Definition 4.5 and Theorem 4.6, p. 54).
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
