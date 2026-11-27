# Reachability and safety games are positionally determined and solvable in linear time

Let $\mathcal{A}$ be an [arena](arenas-strategies-and-memory-structures.md) on a graph with $m$ edges, and $\mathrm{Win} \subseteq V$. The
*reachability* condition $\mathrm{Reach}(\mathrm{Win})$ is the set of infinite plays visiting $\mathrm{Win}$, and the *safety* condition
$\mathrm{Safe}(\mathrm{Win})$ the set of plays never visiting $\mathrm{Win}$; the two are dual, $\mathrm{Paths}^\omega \setminus \mathrm{Reach}(\mathrm{Win}) = \mathrm{Safe}(\mathrm{Win})$.

Reachability games are uniformly positionally determined: there are positional strategies $\sigma$ for Eve and $\tau$ for Adam
winning from every vertex of $W_{\mathrm{Eve}}$ and of $W_{\mathrm{Adam}}$ respectively. The winning region of Eve is the
[attractor](../parity-games/attractor.md) $\mathrm{Attr}_{\mathrm{Eve}}(\mathrm{Win}) = \bigcup_k \mathrm{Attr}^k_{\mathrm{Eve}}(\mathrm{Win})$, where
$\mathrm{Attr}^0_{\mathrm{Eve}}(\mathrm{Win}) = \emptyset$ and $\mathrm{Attr}^{k+1}_{\mathrm{Eve}}(\mathrm{Win}) = \mathrm{Win} \cup \mathrm{Pre}_{\mathrm{Eve}}(\mathrm{Attr}^k_{\mathrm{Eve}}(\mathrm{Win}))$, and
the winning regions and uniform positional winning strategies of both players can be computed in time and space $O(m)$ (in the
unit-cost RAM model). By duality the same holds for safety games, with the roles of the players exchanged.

## Depends on

- [Arenas, strategies and memory structures](arenas-strategies-and-memory-structures.md)
- [Attractor](../parity-games/attractor.md)

## Proof depends on

- [Characterization of the attractor](../parity-games/mem-attractor-iff.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 1 (N. Fijalkow, "Introduction"): Section 1.2, the definitions of $\mathrm{Reach}$ and $\mathrm{Safe}$, Theorem 1.1 and Lemma 1.1 (characterization of the winning region by attractors) with their proofs.
