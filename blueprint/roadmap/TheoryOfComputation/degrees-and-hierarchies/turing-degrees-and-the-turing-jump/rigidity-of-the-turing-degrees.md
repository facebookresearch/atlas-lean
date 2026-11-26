# Rigidity of the full Turing-degree order

Represent subsets of $\mathbb N$ by their total Boolean characteristic functions. Use Turing reducibility on the corresponding total partial-natural functions $n\mapsto 0$ or $1$, and take the quotient by mutual reducibility, ordered by the induced reducibility relation. Every order isomorphism of this entire quotient with itself fixes every degree. The statement has no effectiveness, definability, genericity or initial-segment restriction on the isomorphism.

## Depends on

- [Turing reducibility of predicates](turing-reducible-pred.md) is reducibility of total characteristic-function oracles. The degree carrier here is the order quotient restricted to these oracles, not the quotient of all partial natural-valued functions.

## Proof depends on

- Degree invariants recovering each degree under order automorphisms, with separation on the full set of characteristic-function degrees, not merely a fixed cone or definable subclass.

## Expansion

Prove that conversion between a Boolean characteristic function and its total $0/1$ natural oracle preserves reductions in both directions and induces an order isomorphism. Separate the invariance and degree-recovery arguments before transferring rigidity.

## Sources

- OpenAI, [DegreeRigidity.lean, oracle, quotient and `rigidity`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DegreeRigidity.lean#L7-L39).
