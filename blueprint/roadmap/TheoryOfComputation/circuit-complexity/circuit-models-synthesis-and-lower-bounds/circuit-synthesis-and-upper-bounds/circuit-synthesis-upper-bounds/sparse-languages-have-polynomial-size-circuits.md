# Sparse languages have polynomial-size circuits

If the slice $L\cap\{0,1\}^n$ of a language contains at most $k$ words, then it has a De Morgan circuit with at most $k(2n+2)+1$ gates. Hence every sparse language (polynomially many words of each length; in particular every unary language $L\subseteq 1^*$) belongs to $\mathsf{P}/\mathsf{poly}$.

## Proof sketch

The slice is the disjunction of the minterms of its at most $k$ words; each minterm uses at most $2n$ gates and the disjunction at most $k$ more.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [Polynomial time with polynomial advice](../../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [Sparse decision problems](../../../../complexity-classes/mahaney-s-theorem/sparse.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
