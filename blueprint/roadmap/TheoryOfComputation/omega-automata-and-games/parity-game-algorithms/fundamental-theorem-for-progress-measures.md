# Fundamental theorem for progress measures

Let $\mathcal{G}$ be a finite [parity game](../parity-games/parity-game.md) and $v$ a vertex. Eve wins from $v$ if and only if there are a tree $t$ of some height $h$, with all priorities of $\mathcal{G}$ in $\{1, \dots, 2h\}$, and a
[progress measure](ordered-trees-and-progress-measures.md) $\mu : V \to Y_t \cup \{\top\}$ with $\mu(v) \ne \top$. The proof first treats one-player parity
graphs, where a graph satisfies parity from $v$ (every cycle reachable from $v$ has even maximal priority) exactly when some progress
measure is not $\top$ at $v$, and then applies this to the graph left by a positional winning strategy.

## Depends on

- [Parity game](../parity-games/parity-game.md)
- [Ordered trees and progress measures](ordered-trees-and-progress-measures.md)

## Proof depends on

- [Finite parity games are positionally determined](../parity-games/finite-parity-games-are-positionally-determined.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.5, Theorem 2.8 and Lemma 2.13 (the fundamental lemma for parity graphs) with their proofs.
