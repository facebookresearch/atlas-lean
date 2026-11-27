# PF contains search problems outside PC

There is a polynomially bounded relation $R$ whose search problem is solvable in polynomial time ($R\in\mathsf{PF}$) but which is not polynomial-time decidable, so $R\notin\mathsf{PC}$.

## Proof sketch

Let $R=\{(x,1): x\in H\}\cup\{(x,0): x\in\{0,1\}^*\}$ for an undecidable $H$ such as the self-halting set: the constant solver outputting $0$ always succeeds, yet deciding $(x,1)\in R$ decides $H$.

## Depends on

- [Self-reducible search problems (Goldreich's PC and PF)](self-reducible-search-problems.md)
- [Halting set](../../../degrees-and-hierarchies/turing-reducibility/halting-set.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 2.1.
