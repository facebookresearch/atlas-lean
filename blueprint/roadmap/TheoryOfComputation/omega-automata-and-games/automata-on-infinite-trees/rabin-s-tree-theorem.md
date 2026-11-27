# Rabin's tree theorem

The theory S2S of [monadic second-order logic of two successors](monadic-second-order-logic-of-two-successors.md) is decidable (Rabin). A
sentence is translated into an input-free tree automaton that has a successful run exactly when the sentence is true in the binary tree,
and the existence of a successful run is decidable. The monadic second-order theory of the full tree with $\omega$ successor functions is also
decidable, and hence so is that of the full tree with $n$ successor functions for every finite $n$ (Rabin); this does not extend to
arbitrary trees of bounded branching.

## Depends on

- [Monadic second-order logic of two successors](monadic-second-order-logic-of-two-successors.md)

## Proof depends on

- [Monadic second-order formulas over the binary tree and tree automata](mso-formulas-over-the-binary-tree-and-tree-automata.md)
- [Rabin's basis theorem](rabin-s-basis-theorem.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Theorem 6.20, the argument before it, and the remark after it on trees with finite and countable branching.
- M. O. Rabin, "Decidability of second-order theories and automata on infinite trees", *Transactions of the American Mathematical Society* 141:1–35, 1969: Theorem 1.1 (decidability of S2S), Theorems 1.6 and 1.7, and Theorem 1.12 ($\omega$ successor functions).
- M. O. Rabin, "Decidability of second-order theories and automata on infinite trees", *Transactions of the American Mathematical Society* 141, 1969, pp. 1–35: Theorem 1.1 (S2S), Theorem 1.12 (S$\omega$S) and the remark after Theorem 1.1 that S$n$S for every finite $n$ and S$\omega$S are decidable.
