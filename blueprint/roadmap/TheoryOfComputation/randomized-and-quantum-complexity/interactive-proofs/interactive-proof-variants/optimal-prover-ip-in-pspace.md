# Optimal provers and IP ⊆ PSPACE

For every interactive proof with a polynomial-time private-coin verifier, there is an optimal prover maximizing the acceptance probability on each input, and that maximum is computable in polynomial space by evaluating the game tree over verifier coins and prover messages with an explicit stack; hence $\mathsf{IP}\subseteq\mathsf{PSPACE}$. Sequential repetition $k$ times of a proof system with perfect completeness and soundness error $\varepsilon$, accepting iff all runs accept, gives soundness error $\varepsilon^{k}$.

## Proof sketch

The value of a node of the interaction tree is the maximum over prover messages of the average over consistent verifier coins; depth-first evaluation with exact rational arithmetic keeps polynomially many bits per level.

## Depends on

- [The class IP](../../../complexity-classes/time-and-space-complexity-classes/ip.md)
- [Polynomial space for decision problems](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 8.
- Shafi Goldwasser, Silvio Micali and Charles Rackoff, "The Knowledge Complexity of Interactive Proof Systems", SIAM Journal on Computing 18(1), 186–208, 1989.
