# Characterization of locally testable languages

A language $L \subseteq A^+$ is [locally testable](locally-testable-languages.md) if and only if its syntactic semigroup $S(L)$ is finite and *locally idempotent and
commutative*: for every idempotent $e$, the local monoid $eSe$ is idempotent and commutative; equivalently, $S(L)$ satisfies the identities
$x^\omega y x^\omega z x^\omega = x^\omega z x^\omega y x^\omega$ and $x^\omega y x^\omega y x^\omega = x^\omega y x^\omega$ (Brzozowski and Simon; McNaughton). Since these conditions
can be checked on a finite semigroup, it is decidable whether a regular language is locally testable.

## Depends on

- [Locally testable languages](locally-testable-languages.md)
- [Syntactic monoid](../syntactic-monoid/syntactic-monoid.md)

## Expansion

This page becomes ready once:

- The proof of the characterization, which the cited chapter only attributes and outlines; a source check of J. A. Brzozowski and I. Simon, "Characterizations of locally testable events", *Discrete Mathematics* 4, 1973, and of R. McNaughton, "Algebraic decision procedures for local testability", *Mathematical Systems Theory* 8, 1974 (proof prerequisites and source check; not yet stated)

## Sources

- J.-É. Pin, "Syntactic semigroups", in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 1, Springer, 1997, pp. 679–746, author's copy <https://www.irif.fr/~jep/PDF/HandBook.pdf>: Section 5.3, Theorem 5.19, the attribution to Brzozowski and Simon and to McNaughton before it, and the definition of locally commutative semigroups in Section 4.1.
