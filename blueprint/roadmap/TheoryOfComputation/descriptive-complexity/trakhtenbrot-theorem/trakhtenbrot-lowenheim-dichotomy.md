# Trakhtenbrot–Löwenheim decidability dichotomy for finite satisfiability

Let $\sigma$ be a finite relational vocabulary. The following are equivalent: (1) finite satisfiability of first-order sentences over $\sigma$ is decidable; (2) finite validity over $\sigma$ is decidable; (3) finite validity over $\sigma$ is recursively enumerable; (4) every relation symbol of $\sigma$ has arity at most $1$. Over monadic vocabularies satisfiability and finite satisfiability coincide and are decidable by the small model property.

## Proof sketch

(4)⇒(1): Löwenheim's small model property bounds the size of a model of a monadic sentence, so finite satisfiability reduces to finitely many fixed-size checks. Otherwise a symbol of arity $\ge 2$ makes the problem undecidable and finite validity non-r.e. by Trakhtenbrot's theorem; (2)⇒(3) is trivial and (3) with r.e. finite satisfiability gives decidability.

## Depends on

- [Finite satisfiability and finite validity](finite-satisfiability-and-validity.md)

## Proof depends on

- [Trakhtenbrot's theorem for any vocabulary with a relation of arity at least two](trakhtenbrot-theorem-fixed-vocabulary.md)
- [EF games on monadic structures and the monadic small model property](../ehrenfeucht-fraisse-games/monadic-ef-games-small-model-property.md)
- [Finite satisfiability is recursively enumerable](finite-satisfiability-recursively-enumerable.md)

## Sources

- B. A. Trakhtenbrot, "Impossibility of an Algorithm for the Decision Problem in Finite Classes", Doklady Akademii Nauk SSSR 70, 569–572, 1950.
- L. Löwenheim, "Über Möglichkeiten im Relativkalkül", Mathematische Annalen 76, 447–470, 1915.
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
