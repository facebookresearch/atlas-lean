---
article_id: af_b8846ac6b0b3bf21b86260dd
declaration: structure
origin: cited
statement: formalized
lean: TuringMachine.TM
---

# Definition: Turing Machine

A Turing Machine (TM) is a 7-tuple $(Q, \Sigma, \Gamma, \delta, q_0, q_{\mathrm{acc}}, q_{\mathrm{rej}})$ where $\Sigma$ is the input alphabet, $\Gamma$ is the tape alphabet ($\Sigma \subseteq \Gamma$), and $\delta \colon Q \times \Gamma \to Q \times \Gamma \times \{L, R\}$ is the transition function ($L$ = Left, $R$ = Right). On input $w$ a TM $M$ may halt (enter $q_{\mathrm{acc}}$ or $q_{\mathrm{rej}}$) or $M$ may run forever (loop). So $M$ has 3 possible outcomes for each input $w$: (1) Accept $w$ (enter $q_{\mathrm{acc}}$), (2) Reject $w$ by halting (enter $q_{\mathrm{rej}}$), (3) Reject $w$ by looping (running forever).

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 5, TM — Formal Definition](../../../../../sources/v1/TheoryOfComputation.md)
