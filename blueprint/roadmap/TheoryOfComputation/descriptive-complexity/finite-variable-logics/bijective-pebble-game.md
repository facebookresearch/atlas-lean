# Hella's bijective $k$-pebble game

The *bijective $k$-pebble game* on finite structures $\mathfrak{A}, \mathfrak{B}$ with $|A| = |B|$ uses $k$ pairs of pebbles. Each round, Spoiler picks a pair $i$; Duplicator answers with a bijection $f : A \to B$; Spoiler then places the $\mathfrak{A}$-pebble of pair $i$ on any $c \in A$, which puts the $\mathfrak{B}$-pebble of pair $i$ on $f(c)$. Duplicator wins a play if the pebbled pairs define a partial isomorphism in the initial position and after every round. If $|A| \ne |B|$ no bijection exists, so Duplicator loses as soon as a round is played; a play of $0$ rounds is won iff the initial position is a partial isomorphism.

## Depends on

- [The $k$-pebble game](k-pebble-game.md)

## Sources

- L. Hella, "Logical Hierarchies in PTIME", Information and Computation 129(1), 1–19, 1996.
- J.-Y. Cai, M. Fürer and N. Immerman, "An Optimal Lower Bound on the Number of Variables for Graph Identification", Combinatorica 12(4), 389–410, 1992.
