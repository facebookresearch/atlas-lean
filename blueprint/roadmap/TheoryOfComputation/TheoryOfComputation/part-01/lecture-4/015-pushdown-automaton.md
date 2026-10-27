---
article_id: af_255d7d6f3f40fe108f81815a
declaration: structure
origin: cited
statement: formalized
lean: PDA
---

# Definition (Pushdown Automaton)

A Pushdown Automaton (PDA) is a 6-tuple $(Q, \Sigma, \Gamma, \delta, q_0, F)$ where $\Sigma$ is the input alphabet, $\Gamma$ is the stack alphabet, and $\delta \colon Q \times \Sigma_\varepsilon \times \Gamma_\varepsilon \to \mathcal{P}(Q \times \Gamma_\varepsilon)$. Accept if some thread is in the accept state at the end of the input string.

## Depends on

- [Definition (Nondeterministic Finite Automaton)](../lecture-2/009-nondeterministic-finite-automaton.md)

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 4, section on PDA — Formal Definition](../../../../../sources/v1/TheoryOfComputation.md)
