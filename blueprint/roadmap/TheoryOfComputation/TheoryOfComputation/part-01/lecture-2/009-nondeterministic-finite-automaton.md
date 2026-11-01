---
article_id: af_52c20759b108b16514968ff0
declaration: structure
origin: cited
statement: formalized
lean: Sipser.NFA
---

# Definition (Nondeterministic Finite Automaton)

A nondeterministic finite automaton (NFA) $N$ is a 5-tuple $(Q, \Sigma, \delta, q_0, F)$ where all components are the same as for a DFA except $\delta \colon Q \times \Sigma_\varepsilon \to \mathcal{P}(Q)$, where $\Sigma_\varepsilon = \Sigma \cup \{\varepsilon\}$ and $\mathcal{P}(Q) = \{R \mid R \subseteq Q\}$ is the power set of $Q$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 2, NFA — Formal Definition](../../../../../sources/v1/TheoryOfComputation.md)
