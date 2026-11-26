# Memory requirements of Muller games

Let $\mathrm{Muller}(\mathcal{F})$ be a [Muller objective](muller-rabin-and-streett-objectives.md) and $m_{\mathcal{F}}$ the number defined
from its [Zielonka tree](zielonka-tree-of-a-muller-condition.md). In every game with condition $\mathrm{Muller}(\mathcal{F})$, from every
vertex either Eve has a winning strategy using a memory structure of size $m_{\mathcal{F}}$ or Adam has a winning strategy. The
bound is tight whenever some nonempty set of colors belongs to $\mathcal{F}$: then some game with condition $\mathrm{Muller}(\mathcal{F})$ is won by Eve
with $m_{\mathcal{F}}$ memory states and not with fewer, even in games whose colors are given by a partial coloring of the edges (Dziembowski,
Jurdziński and Walukiewicz). If no nonempty set belongs to $\mathcal{F}$, Eve wins no play.

## Depends on

- [Muller, Rabin and Streett objectives](muller-rabin-and-streett-objectives.md)
- [Zielonka tree of a Muller condition](zielonka-tree-of-a-muller-condition.md)
- [Arenas, strategies and memory structures](arenas-strategies-and-memory-structures.md)

## Proof depends on

- [Büchi–Landweber theorem](buchi-landweber-theorem.md)

## Expansion

This page becomes ready once:

- The lower-bound construction of a game in which Eve needs $m_{\mathcal{F}}$ memory states, which the cited survey does not construct, from S. Dziembowski, M. Jurdziński and I. Walukiewicz, "How much memory is needed to win infinite games?", *Proceedings of the 12th IEEE LICS*, 1997 (proof prerequisite and source check; not yet stated)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 3 (N. Fijalkow and F. Horn, "Regular games"): Theorem 3.9, the proof of its upper bound with Lemmas 3.4 and 3.5, and Definition 3.2.
