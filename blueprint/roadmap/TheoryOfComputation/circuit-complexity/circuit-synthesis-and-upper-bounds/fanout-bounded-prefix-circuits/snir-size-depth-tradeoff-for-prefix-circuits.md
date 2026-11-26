# Snir's size–depth trade-off for prefix circuits

Every prefix circuit on $N\ge1$ inputs satisfies $c+d\ge 2N-2$, where $c$ is the number of binary gates and $d$ the depth. Hence zero-deficiency circuits are exactly those meeting this bound.

## Proof sketch

Along a longest path to the last output, each of the $d$ levels contributes at most one binary gate computing a prefix on that path; the remaining $N-1-d$ outputs not on the critical path each need a distinct further gate, and the $N-1$ binary gates of the last output's tree are needed as well; summing gives $c\ge 2N-2-d$.

## Depends on

- [Universal prefix circuits and fanout-bounded optimality](universal-prefix-circuits.md)

## Sources

- Marc Snir, "Lower Bounds on Probabilistic Linear Decision Trees", Theoretical Computer Science, 1985.
- Igor S. Sergeev, "A Note on the Depth of Optimal Fanout-Bounded Prefix Circuits", 2025.
