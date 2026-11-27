# EF games on finite linear orders: the $2^n - 1$ threshold

Duplicator wins the $n$-round Ehrenfeucht–Fraïssé game on two finite linear orders $L_1, L_2$ (the empty order included, and $n \ge 0$) if and only if $|L_1| = |L_2|$ or both $|L_1|, |L_2| \ge 2^n - 1$. Consequently a first-order sentence of quantifier rank $n$ over the order $\le$ has the same truth value on all finite linear orders with at least $2^n - 1$ elements, and for $|L_1| \ne |L_2|$ with $\min(|L_1|,|L_2|) < 2^n - 1$ some rank-$n$ sentence distinguishes them.

## Proof sketch

Duplicator maintains the invariant that corresponding gaps between consecutive pebbles have equal length or both have length at least $2^{j} - 1$ with $j$ rounds left; she answers a move in a long gap by splitting the corresponding long gap appropriately. Spoiler wins on unequal small orders by binary search.

## Depends on

- [Duplicator wins the EF game iff there is a back-and-forth system](ef-game-back-and-forth.md)
- [Quantifier rank and rank-$n$ equivalence](../finite-structures-and-definability/quantifier-rank.md)

## Proof depends on

- [Rank-$n$ types coincide with $n$-round game equivalence](rank-types-and-game-equivalence.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004: Theorem 3.6 (orders of length at least $2^k$ are $k$-equivalent) and Exercise 3.7 (the tight bound).
- J. G. Rosenstein, Linear Orderings, Academic Press, 1982 (the exact threshold $2^n - 1$).
- P. G. Kolaitis, "On the Expressive Power of Logics on Finite Models", in Finite Model Theory and Its Applications, Springer, 2007.
