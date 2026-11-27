# Hanf locality of first-order logic

For all $n, k$: if $(\mathfrak{A}, \bar a) \leftrightarrows_d (\mathfrak{B}, \bar b)$ for finite structures with $d = (3^n - 1)/2$, then Duplicator wins the $n$-round EF game from $(\bar a,\bar b)$, so $(\mathfrak{A},\bar a) \equiv_n (\mathfrak{B},\bar b)$. In particular finite structures whose elements can be matched by a bijection preserving isomorphism types of $(3^n-1)/2$-neighborhoods satisfy the same sentences of quantifier rank $n$.

## Proof sketch

Induction on $n$: Hanf equivalence at radius $3d + 1$ is preserved, at radius $d$, by adding a matched pair; given a Spoiler move $c$ answer with $f(c)$ and use a gluing of neighborhood isomorphisms away from the old pebbles.

## Depends on

- [Hanf equivalence](hanf-equivalence.md)
- [Duplicator wins the EF game iff there is a back-and-forth system](../ehrenfeucht-fraisse-games/ef-game-back-and-forth.md)

## Proof depends on

- [Rank-$n$ types coincide with $n$-round game equivalence](../ehrenfeucht-fraisse-games/rank-types-and-game-equivalence.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004: Corollary 4.10 and Theorem 4.12 ($\mathrm{hlr} \le (3^k - 1)/2$ for quantifier rank $k$).
- R. Fagin, L. Stockmeyer and M. Y. Vardi, "On Monadic NP vs Monadic co-NP", Information and Computation 120(1), 78–92, 1995.
