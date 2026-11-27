# Decidability of S1S

The theory S1S, the set of monadic second-order sentences true in $(\mathbb{N}, S, <)$ with set variables ranging over arbitrary
sets of natural numbers, is decidable (Büchi). A sentence is translated into an input-free Büchi automaton that has a
successful run exactly when the sentence is true, and such a run exists exactly when some state reachable from the initial
state lies on a cycle through a final state.

## Depends on

- [Monadic second-order logic over words](../logic-and-tree-automata/monadic-second-order-logic-over-words.md)

## Proof depends on

- [Büchi's theorem on monadic second-order logic over infinite words](buchi-s-theorem-on-infinite-words.md)
- [Lasso characterization of Büchi nonemptiness](../emptiness-of-b-chi-automata/language-nonempty-iff-has-lasso.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Corollary 5.10 and its proof.
