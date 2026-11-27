# A language outside P/poly

There is a language $L\subseteq\{0,1\}^*$ such that for all sufficiently large $n$ the slice $L\cap\{0,1\}^n$ has De Morgan circuit complexity greater than $2^n/n$; in particular $L\notin\mathsf{P}/\mathsf{poly}$.

## Proof sketch

For each large $n$ choose as the slice a function of complexity above $2^n/n$, which exists by Shannon's counting argument; $2^n/n$ eventually exceeds every polynomial.

## Depends on

- [Polynomial time with polynomial advice](../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [Circuit complexity, binary cost and formula leaf size](../circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Shannon's sharp counting bound: almost all functions need more than 2^n/n gates](../circuit-models-and-complexity-measures/shannon-sharp-circuit-size-lower-bound.md)

## Sources

- Claude E. Shannon, "The Synthesis of Two-Terminal Switching Circuits", Bell System Technical Journal, 1949.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
