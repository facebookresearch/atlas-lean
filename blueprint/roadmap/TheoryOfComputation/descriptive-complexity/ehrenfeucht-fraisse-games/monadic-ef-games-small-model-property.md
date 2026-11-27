# EF games on monadic structures and the monadic small model property

Let $\sigma$ be a relational vocabulary all of whose symbols have arity at most one. The *color* of an element is the set of unary symbols it satisfies. If two $\sigma$-structures agree on the nullary symbols and, for every color, have equally many elements of that color or both at least $n$, then Duplicator wins the $n$-round EF game. Consequently (Löwenheim) every satisfiable monadic sentence of quantifier rank $n$ with $u$ unary symbols has a model of size at most $\max(n,1) \cdot 2^u$, obtained as a substructure of any model; in particular satisfiability and finite satisfiability of monadic first-order sentences are decidable.

## Proof sketch

Duplicator answers each element with an element of the same color, fresh if Spoiler's element is fresh, which is possible while fewer than $n$ elements of a color are pebbled. Truncating every color class to at most $n$ elements preserves the game, hence the sentence.

## Depends on

- [Duplicator wins the EF game iff there is a back-and-forth system](ef-game-back-and-forth.md)

## Proof depends on

- [Rank-$n$ types coincide with $n$-round game equivalence](rank-types-and-game-equivalence.md)

## Sources

- L. Löwenheim, "Über Möglichkeiten im Relativkalkül", Mathematische Annalen 76, 447–470, 1915.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- E. Börger, E. Grädel and Y. Gurevich, The Classical Decision Problem, Springer, 1997 (the Löwenheim class with equality and its small model property).
