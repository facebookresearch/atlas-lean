---
article_id: af_3baaf6a3a1ef4dff89b24c58
declaration: def
origin: cited
statement: formalized
lean: DFA.language
---

# Definition (M accepts string w)

$M$ accepts string $w = w_1 w_2 \ldots w_n$, each $w_i \in \Sigma$, if there is a sequence of states $r_0, r_1, r_2, \ldots, r_n \in Q$ where $r_0 = q_0$, $r_i = \delta(r_{i-1}, w_i)$ for $1 \leq i \leq n$, and $r_n \in F$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 1, Finite Automata — Computation](../../../../../sources/v1/TheoryOfComputation.md)
