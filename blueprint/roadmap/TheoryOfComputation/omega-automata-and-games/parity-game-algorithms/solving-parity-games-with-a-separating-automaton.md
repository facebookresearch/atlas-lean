# Solving parity games with a separating automaton

Let $A$ be a deterministic $(n, d)$-[separating automaton](separating-automata-for-parity-games.md) with a safety acceptance
condition. Then the winning regions of every parity game with $n$ vertices, $m$ edges and priorities in $\{1, \dots, d\}$ can be
computed in time $O(m \cdot |A|)$, where $|A|$ is the number of states of $A$: Eve wins the parity game from $v$ exactly when she
wins the safety game played on the product of the game with $A$ from $v$ and the initial state of $A$, and safety games are
solved in time linear in their number of edges by an attractor computation.

## Depends on

- [Separating automata for parity games](separating-automata-for-parity-games.md)
- [Winning region of a parity game](../parity-games/winning-region.md)

## Proof depends on

- [Finite parity games are positionally determined](../parity-games/finite-parity-games-are-positionally-determined.md)
- [Attractor](../parity-games/attractor.md)

## Expansion

This page becomes ready once:

- Safety and reachability games on finite arenas are positionally determined and solvable in time linear in the number of edges (proof prerequisite; not yet stated)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Lemma 2.8 (game equivalence using separating automata) and Theorem 2.4 with its proof, which uses Theorem 1.1 of Chapter 1 for safety games.
