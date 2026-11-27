# Positionally determined Muller conditions are the Rabin conditions

Let $\mathrm{Muller}(\mathcal{F})$ be a [Muller objective](muller-rabin-and-streett-objectives.md).

- $\mathrm{Muller}(\mathcal{F})$ is positionally determined (for Eve) if and only if it is a Rabin objective, that is, $2^C \setminus \mathcal{F}$
  is closed under union.
- $\mathrm{Muller}(\mathcal{F})$ is bi-positionally determined if and only if it is a parity objective: there is a map $p : C \to \mathbb{N}$ such that a nonempty set $X \subseteq C$ belongs to $\mathcal{F}$ exactly when the largest value of $p$ on $X$ is even.

In terms of the [Zielonka tree](zielonka-tree-of-a-muller-condition.md), Eve is positional exactly when every node labelled by
a set in $\mathcal{F}$ has at most one child, that is, when $m_{\mathcal{F}} = 1$.

## Depends on

- [Zielonka tree of a Muller condition](zielonka-tree-of-a-muller-condition.md)
- [Muller, Rabin and Streett objectives](muller-rabin-and-streett-objectives.md)
- [Arenas, strategies and memory structures](arenas-strategies-and-memory-structures.md)

## Proof depends on

- [Memory requirements of Muller games](memory-requirements-of-muller-games.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 3 (N. Fijalkow and F. Horn, "Regular games"): Theorem 3.10 and its proof, where the Zielonka tree of a bi-positional condition is a chain and the levels of the chain give the priorities.
