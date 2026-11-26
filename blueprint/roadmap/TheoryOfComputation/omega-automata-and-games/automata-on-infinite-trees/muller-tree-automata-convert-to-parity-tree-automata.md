# Muller tree automata convert to parity tree automata

For every Muller tree automaton one can construct a parity tree automaton accepting the same infinite trees, in the sense of
[tree automata on infinite trees](tree-automata-on-infinite-trees.md); conversely, every parity tree automaton is a Muller tree
automaton. The construction runs the given automaton and keeps, in its state, the order of the latest visits to the states of the
given automaton together with the position of the last change (an order vector with hit); the hit position, together with whether
the set of states listed from it onwards belongs to $\mathcal{F}$, provides the parity index.

## Depends on

- [Tree automata on infinite trees](tree-automata-on-infinite-trees.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Theorem 6.5, Remark 6.6 and the proof of Theorem 6.5, and the remark before it on converting parity tree automata into Muller tree automata.
