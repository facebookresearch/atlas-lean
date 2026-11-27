# Languages of Büchi automata are MSO-definable

For every nondeterministic [Büchi automaton](../emptiness-of-b-chi-automata/mem-language-iff.md) $\mathcal{A} = (Q, A, q_0, \Delta, F)$ with $Q = \{0, \dots, k\}$ and
$q_0 = 0$ there is a sentence of [monadic second-order logic](../logic-and-tree-automata/monadic-second-order-logic-over-words.md) with successor that holds in exactly the
infinite words accepted by $\mathcal{A}$, constructed effectively. It states the existence of pairwise disjoint sets $X_0, \dots, X_k$ covering all positions and coding a run
($X_i$ is the set of positions where the state is $i$) such that the first position is in $X_0$, every pair of consecutive positions
$x, y$ with $x \in X_i$, $y \in X_j$ and letter $a$ at $x$ satisfies $(i, a, j) \in \Delta$, and infinitely many positions lie in $\bigcup_{i \in F} X_i$
(for every position some later position does).

## Depends on

- [Monadic second-order logic over words](../logic-and-tree-automata/monadic-second-order-logic-over-words.md)
- [Büchi acceptance condition](../emptiness-of-b-chi-automata/mem-language-iff.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): proof of Theorem 3.1 (the sentence describing a successful run) and proof of Theorem 5.9 (changing the acceptance clause to "infinitely often a final state occurs").
