# Rabin's basis theorem

For parity tree automata $\mathcal{A}$, in the sense of [tree automata on infinite trees](tree-automata-on-infinite-trees.md), it is decidable
whether $T^\omega(\mathcal{A})$ is empty, and every nonempty $T^\omega(\mathcal{A})$ contains a [regular tree](regular-infinite-trees.md), whose
generating automaton is obtained effectively from $\mathcal{A}$ (Rabin). After completing $\mathcal{A}$ by a rejecting sink state, the automaton that guesses its
input tree has a successful run exactly when Automaton wins a finite parity game derived from it, which is decidable, and a positional winning strategy in that game is
a finite deterministic automaton generating an accepted regular tree.

## Depends on

- [Tree automata on infinite trees](tree-automata-on-infinite-trees.md)
- [Regular infinite trees](regular-infinite-trees.md)

## Proof depends on

- [Acceptance of a tree as a game](acceptance-of-a-tree-as-a-game.md)
- [Finite parity games are positionally determined](../parity-games/finite-parity-games-are-positionally-determined.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Theorem 6.18 and its proof, Example 6.12 (the finite game of an input-free automaton) and Theorem 6.16 (effective determinacy of finite-state games).
