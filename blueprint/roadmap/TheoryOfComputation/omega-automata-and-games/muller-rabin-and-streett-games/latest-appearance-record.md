# Latest appearance records turn Muller conditions into parity conditions

Let $C = \{1, \dots, d\}$ and let $\mathrm{Muller}(\mathcal{F})$ be a [Muller objective](muller-rabin-and-streett-objectives.md). There is
a deterministic parity automaton over the alphabet $C$, with acceptance on transitions, that accepts exactly the words in
$\mathrm{Muller}(\mathcal{F})$, has $d!$ states and uses priorities in $\{1, \dots, 2d\}$. Its states are the orderings of $C$; reading a
color moves it to the front, and the priority of the transition is determined by the position the color came from and by
whether the set of colors in front of that position belongs to $\mathcal{F}$. With acceptance on states the same construction
needs $d \cdot d!$ states (the order vector with a hit position). Taking the product of a Muller game with this automaton reduces
it to a parity game.

## Depends on

- [Muller, Rabin and Streett objectives](muller-rabin-and-streett-objectives.md)
- [Nondeterministic parity automaton](../parity-automata/parity.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 3 (N. Fijalkow and F. Horn, "Regular games"): Theorem 3.5 (the latest appearance record construction) with its proof and the remark on $d \cdot d!$ states.
- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Theorem 6.5 and Remark 6.6 (order vectors with hit, credited to Büchi and to the latest appearance records of Gurevich and Harrington).
