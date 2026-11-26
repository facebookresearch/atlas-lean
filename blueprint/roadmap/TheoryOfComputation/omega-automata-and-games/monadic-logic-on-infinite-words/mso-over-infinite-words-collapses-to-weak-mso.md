# Monadic second-order logic over infinite words collapses to weak monadic logic

Over infinite words, every formula $\varphi(X_1, \dots, X_n)$ of [monadic second-order logic](../logic-and-tree-automata/monadic-second-order-logic-over-words.md) is equivalent to a formula of
weak monadic second-order logic, in which set quantifiers range only over finite sets. More precisely, $\varphi$ is equivalent
over $(\{0, 1\}^n)^\omega$ to a finite disjunction of formulas
$\exists x \forall y (x < y \to \neg \varphi_i(X, y)) \wedge \forall x \exists y (x < y \wedge \psi_i(X, y))$ in which $\varphi_i$ and $\psi_i$
quantify only over positions and finite sets below $y$.

## Depends on

- [Monadic second-order logic over words](../logic-and-tree-automata/monadic-second-order-logic-over-words.md)

## Proof depends on

- [Büchi's theorem on monadic second-order logic over infinite words](buchi-s-theorem-on-infinite-words.md)

## Expansion

This page becomes ready once:

- McNaughton's theorem, that every language of a Büchi automaton is recognized by a deterministic Rabin or Muller automaton (proof prerequisite; not yet on the graph)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Proposition 5.11 and Corollary 5.12, with the argument before them.
