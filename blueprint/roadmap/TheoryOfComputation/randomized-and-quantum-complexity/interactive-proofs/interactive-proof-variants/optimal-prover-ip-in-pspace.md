# Optimal provers and IP ⊆ PSPACE

For every interactive proof with a polynomial-time private-coin verifier, there is an optimal prover maximizing the acceptance probability on each input, and that maximum is computable in polynomial space by evaluating the game tree over verifier coins and prover messages with an explicit stack; hence $\mathsf{IP}\subseteq\mathsf{PSPACE}$.

## Proof sketch

The value of a node of the interaction tree is the maximum over prover messages of the average over consistent verifier coins; depth-first evaluation with exact rational arithmetic keeps polynomially many bits per level.

Derived (not stated in the cited sources): sequential repetition $k$ times of a proof system with perfect completeness and soundness error $\varepsilon$, accepting iff all runs accept, keeps perfect completeness and gives soundness error $\varepsilon^{k}$. For a false input, whatever the prover did in earlier runs, the conditional probability that the next run accepts is at most $\varepsilon$, since the verifier's coins in that run are fresh; multiplying the $k$ conditional probabilities gives $\varepsilon^{k}$.

## Depends on

- [The class IP](../../../complexity-classes/time-and-space-complexity-classes/ip.md)
- [Polynomial space for decision problems](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 8 (Remark 8.6(2) of the January 2007 web draft on the authors' homepage: the optimum prover can be computed in polynomial space, "Thus IP $\subseteq$ PSPACE").
- Shafi Goldwasser, Silvio Micali and Charles Rackoff, "The Knowledge Complexity of Interactive Proof Systems", SIAM Journal on Computing 18(1), 186–208, 1989.
