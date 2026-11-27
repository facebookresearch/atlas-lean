# The $k$-pebble game

The *$k$-pebble game* on structures $\mathfrak{A}, \mathfrak{B}$ uses $k$ pairs of pebbles. In each round Spoiler picks a pair $i$, places (or moves) the $\mathfrak{A}$-pebble or the $\mathfrak{B}$-pebble of pair $i$ on an element of that structure, and Duplicator places the other pebble of pair $i$ on an element of the other structure. Duplicator wins a play of $n$ rounds (respectively of infinitely many rounds) if the pebbled pairs define a partial isomorphism in the initial position and after every round; in particular a play of $0$ rounds is won iff the initial position is a partial isomorphism, and the empty initial position always is. A *pebble back-and-forth system* is a nonempty family of partial isomorphisms with domains of size at most $k$, closed under restriction, such that every member with fewer than $k$ pairs satisfies the back and forth conditions.

## Depends on

- [Partial isomorphisms between pointed structures](../ehrenfeucht-fraisse-games/partial-isomorphisms.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
