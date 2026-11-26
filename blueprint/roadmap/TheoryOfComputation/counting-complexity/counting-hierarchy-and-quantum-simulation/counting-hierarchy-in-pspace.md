# The counting hierarchy is contained in PSPACE

Every level of the counting hierarchy is contained in $\mathsf{PSPACE}$: $\mathsf{CH}\subseteq\mathsf{PSPACE}$. More generally, $\mathsf{PP}^{A}\subseteq\mathsf{PSPACE}$ for every $A\in\mathsf{PSPACE}$, and exact accepting-path counts of polynomial-time machines relative to $\mathsf{PSPACE}$ oracles are computable in polynomial space.

## Proof sketch

Induction on the level: count accepting computation paths one at a time with a polynomial-size counter, answering each oracle query by the polynomial-space algorithm for the previous level, reusing space.

## Depends on

- [The counting hierarchy CH](counting-hierarchy.md)
- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [PP is contained in PSPACE](../unbounded-error-probabilistic-time-pp/pp-subset-pspace.md)

## Sources

- Klaus W. Wagner, "The Complexity of Combinatorial Problems with Succinct Input Representation", Acta Informatica 23(3), 1986.
- Lance Fortnow, "Counting Complexity", Complexity Theory Retrospective II, 1997.
