# Monadic second-order formulas over the binary tree and tree automata

For every formula $\varphi(X_1, \dots, X_n)$ of [monadic second-order logic of two successors](monadic-second-order-logic-of-two-successors.md)
one can effectively construct a Muller tree automaton over $\{0, 1\}^n$, in the sense of [tree automata on infinite trees](tree-automata-on-infinite-trees.md),
that accepts exactly the trees satisfying $\varphi$; conversely, the acceptance of a Muller tree automaton is expressible by such a formula,
which existentially quantifies a run and universally quantifies the paths. Hence a set of infinite trees over $\{0, 1\}^n$ is recognizable if
and only if it is definable in monadic second-order logic over the binary tree (Rabin).

## Depends on

- [Monadic second-order logic of two successors](monadic-second-order-logic-of-two-successors.md)
- [Tree automata on infinite trees](tree-automata-on-infinite-trees.md)

## Proof depends on

- [Complementation of parity tree automata](complementation-of-parity-tree-automata.md)
- [Muller tree automata convert to parity tree automata](muller-tree-automata-convert-to-parity-tree-automata.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Theorem 6.19 and its proof, and the remark after it on formalizing tree automaton acceptance in monadic second-order logic.
