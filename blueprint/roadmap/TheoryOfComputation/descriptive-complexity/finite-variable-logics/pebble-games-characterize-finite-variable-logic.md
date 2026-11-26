# Pebble games characterize $\mathrm{FO}^k$ and $L^k_{\infty\omega}$

For structures $\mathfrak{A}, \mathfrak{B}$ with finitely many relation symbols, positions $\bar a, \bar b$ on at most $k$ pebbles and $n \in \mathbb{N}$: Duplicator wins the $n$-round $k$-pebble game from $(\bar a, \bar b)$ iff $\bar a$ and $\bar b$ satisfy the same $\mathrm{FO}^k$ formulas of quantifier rank at most $n$. Duplicator wins the infinite $k$-pebble game (equivalently there is a pebble back-and-forth system containing the position) iff $\bar a, \bar b$ satisfy the same $L^k_{\infty\omega}$ formulas; on finite structures this is also equivalent to agreeing on all $\mathrm{FO}^k$ formulas.

## Proof sketch

As for Ehrenfeucht–Fraïssé: define $k$-variable rank-$n$ types and their Hintikka formulas, which use only the $k$ variables because a moved pebble frees its variable; the infinite case takes the intersection over $n$, which stabilizes on finite structures, and uses infinitary conjunctions in general.

## Depends on

- [Finite-variable logics $\mathrm{FO}^k$ and $L^k_{\infty\omega}$](finite-variable-logics.md)
- [The $k$-pebble game](k-pebble-game.md)

## Proof depends on

- [Rank-$n$ types coincide with $n$-round game equivalence](../ehrenfeucht-fraisse-games/rank-types-and-game-equivalence.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- Ph. G. Kolaitis and M. Y. Vardi, "Infinitary Logics and 0-1 Laws", Information and Computation 98(2), 258–294, 1992.
