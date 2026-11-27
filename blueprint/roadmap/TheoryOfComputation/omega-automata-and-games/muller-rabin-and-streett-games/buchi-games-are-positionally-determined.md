# Büchi games are positionally determined and solvable in quadratic time

In a game with a *Büchi condition*, Eve wins a play when it visits a given set of vertices infinitely often. Büchi
conditions are uniformly positionally determined: in every Büchi game, Eve has a positional strategy winning from every
vertex of her winning region, and Adam has one winning from every vertex of his. The winning regions of a finite Büchi game
with $n$ vertices and $m$ edges can be computed in time $O(n m)$ and space $O(m)$, by iterating attractor computations.

## Depends on

- [Arenas, strategies and memory structures](arenas-strategies-and-memory-structures.md)

## Proof depends on

- [Attractor](../parity-games/attractor.md)
- [Characterization of the attractor](../parity-games/mem-attractor-iff.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 1 (N. Fijalkow, "Introduction"): Theorem 1.6, with Lemmas 1.5 and 1.6 (fixed-point characterizations of the winning region) and the remark after Theorem 1.6 that positional determinacy also holds for infinite games.
