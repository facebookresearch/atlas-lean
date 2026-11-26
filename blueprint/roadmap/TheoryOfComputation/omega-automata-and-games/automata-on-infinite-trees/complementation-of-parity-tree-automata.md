# Complementation of parity tree automata

For every parity tree automaton $\mathcal{A}$ over an alphabet $A$ one can effectively construct a Muller tree automaton, and hence a
parity tree automaton, that accepts exactly the infinite trees in $T^\omega_A \setminus T^\omega(\mathcal{A})$, in the sense of
[tree automata on infinite trees](tree-automata-on-infinite-trees.md) (Rabin). Thus the recognizable sets of infinite trees are closed
under complementation. After completing $\mathcal{A}$ by a rejecting sink state, so that every play of the acceptance game is infinite: if $\mathcal{A}$ rejects $t$,
Automaton has no winning strategy in the acceptance game, so by positional
determinacy Pathfinder has a positional one; such a strategy is a labelling of the tree by finitely many local instructions, and the
complement automaton guesses this labelling and checks, by a deterministic automaton on infinite words run along every path, that no
path consistent with it satisfies the acceptance condition of $\mathcal{A}$.

## Depends on

- [Tree automata on infinite trees](tree-automata-on-infinite-trees.md)

## Proof depends on

- [Acceptance of a tree as a game](acceptance-of-a-tree-as-a-game.md)
- [Parity games on arbitrary arenas are positionally determined](../muller-rabin-and-streett-games/parity-games-on-arbitrary-arenas-are-positionally-determined.md)
- [Muller tree automata convert to parity tree automata](muller-tree-automata-convert-to-parity-tree-automata.md)

## Expansion

This page becomes ready once:

- McNaughton's theorem, that every language of a Büchi automaton is recognized by a deterministic Muller automaton, used to check the paths of the guessed strategy (proof prerequisite; not yet on the graph)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Theorem 6.8 (determinacy of the acceptance games), Theorem 6.9 (complementation) and its proof.
- M. O. Rabin, "Decidability of second-order theories and automata on infinite trees", *Transactions of the American Mathematical Society* 141:1–35, 1969: Theorem 1.5 (complementation of the sets definable by automata on infinite trees, with Rabin's acceptance condition).
