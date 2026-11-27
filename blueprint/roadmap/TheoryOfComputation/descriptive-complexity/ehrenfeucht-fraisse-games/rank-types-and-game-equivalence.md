# Rank-$n$ types coincide with $n$-round game equivalence

For a vocabulary with finitely many relation symbols, structures $\mathfrak{A}, \mathfrak{B}$ and $k$-tuples $\bar a, \bar b$, the following are equivalent: (1) $\bar a$ and $\bar b$ have the same rank-$n$ type; (2) Duplicator wins the $n$-round Ehrenfeucht–Fraïssé game from $(\bar a, \bar b)$; (3) $\mathfrak{B} \models \varphi^n_{\bar a}(\bar b)$; (4) $(\mathfrak{A},\bar a) \equiv_n (\mathfrak{B},\bar b)$. This proves the Ehrenfeucht–Fraïssé theorem with explicit witnessing formulas, also for formulas with free variables.

## Proof sketch

(1)⇔(2) by induction on $n$: equal type sets mean every extension in one structure is matched in the other. (1)⇒(3) since Hintikka formulas define types. (3)⇒(4) because every rank-$n$ formula is a disjunction of Hintikka formulas. (4)⇒(3) as the Hintikka formula has rank $n$.

## Depends on

- [Rank-$n$ types and Hintikka formulas](hintikka-formulas.md)
- [Duplicator wins the EF game iff there is a back-and-forth system](ef-game-back-and-forth.md)
- [Quantifier rank and rank-$n$ equivalence](../finite-structures-and-definability/quantifier-rank.md)

## Proof depends on

- [Finitely many formulas of bounded quantifier rank up to equivalence](../finite-structures-and-definability/finitely-many-formulas-of-bounded-rank.md)

## Sources

- A. Ehrenfeucht, "An Application of Games to the Completeness Problem for Formalized Theories", Fundamenta Mathematicae 49, 129–141, 1961.
- R. Fraïssé, "Sur quelques classifications des systèmes de relations", Publications Scientifiques de l'Université d'Alger, Série A 1, 35–182, 1954.
- H.-D. Ebbinghaus and J. Flum, Finite Model Theory, 2nd ed., Springer, 1999.
