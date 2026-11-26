# Progress measures over a universal tree characterize the winner

Let $\mathcal{G}$ be a [parity game](../parity-games/parity-game.md) with $n$ vertices and priorities in $\{1, \dots, d\}$, with $d$ even (pad an odd maximal priority by an unused even one), $v$ a vertex and $T$ an
$(n, d/2)$-[universal tree](universal-trees.md). Eve wins from $v$ if and only if there is a [progress measure](ordered-trees-and-progress-measures.md)
$\mu : V \to Y_T \cup \{\top\}$ with $\mu(v) \ne \top$. A single tree therefore serves for all games of the given size, and the least progress measure
over $T$, computed by value iteration, decides the winner everywhere.

## Depends on

- [Parity game](../parity-games/parity-game.md)
- [Ordered trees and progress measures](ordered-trees-and-progress-measures.md)
- [Universal trees](universal-trees.md)

## Proof depends on

- [Fundamental theorem for progress measures](fundamental-theorem-for-progress-measures.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.5, Corollary 2.2 (fundamental corollary for progress measures) with its proof, using Fact 2.6 (embeddings as order-preserving maps of leaves).
