# Weft of a circuit and the W-hierarchy circuit classes

In a Boolean circuit over the unbounded fan-in basis, a gate is *large* if it has more than two arguments. The *weft* of a circuit is the largest number of large gates on a path from an input to the output; equivalently it is the depth computed with weight $1$ for large gates and $0$ for all other gates. For $t\ge 1$, the parameterized class $W[t]$ consists of the parameterized problems that are fpt-reducible to weighted satisfiability of circuits of constant depth and weft at most $t$.

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)
- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)

## Sources

- Marek Cygan, Fedor V. Fomin, Łukasz Kowalik et al., "Parameterized Algorithms", Springer, 2015.
- Rodney G. Downey, Michael R. Fellows, "Parameterized Complexity", Springer, 1999.
