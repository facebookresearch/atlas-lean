# PF contains search problems outside PC

$\mathsf{PF}$ contains (unnatural) search problems that are not in $\mathsf{PC}$; that is, $\mathsf{PF}\not\subseteq\mathsf{PC}$. Since members of $\mathsf{PF}$ are polynomially bounded relations, such a relation is not decidable in polynomial time.

## Proof sketch

Let $R=\{(x,1): x\in H\}\cup\{(x,0): x\in\{0,1\}^*\}$ for an undecidable $H$ such as the self-halting set: the constant solver outputting $0$ always succeeds, yet deciding $(x,1)\in R$ decides $H$.

## Depends on

- [Self-reducible search problems (Goldreich's PC and PF)](self-reducible-search-problems.md)
- [Halting set](../../../degrees-and-hierarchies/turing-reducibility/halting-set.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Section 2.1.1.2 ("PF contains (unnatural) problems that are not in PC") and Section 2.1.3 ("PF is not contained in PC"), with Exercise 2.1.
