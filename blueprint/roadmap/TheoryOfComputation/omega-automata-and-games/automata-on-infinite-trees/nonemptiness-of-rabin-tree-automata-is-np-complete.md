# Nonemptiness of Rabin tree automata is NP-complete

Deciding whether a given Rabin tree automaton, in the sense of [tree automata on infinite trees](tree-automata-on-infinite-trees.md), accepts some
infinite tree is NP-complete, and for automata with $m$ states and $n$ accepting pairs it is solvable in time $O((m n)^{3n})$ (Emerson and
Jutla). Hardness is by a polynomial-time reduction from 3-SAT.

## Depends on

- [Tree automata on infinite trees](tree-automata-on-infinite-trees.md)

## Proof depends on

- [Rabin games are positionally determined for the Rabin player](../muller-rabin-and-streett-games/rabin-games-are-positionally-determined.md)
- [Solving Rabin games is NP-complete](../muller-rabin-and-streett-games/solving-rabin-games-is-np-complete.md)

## Expansion

This page becomes ready once:

- The reduction from the nonemptiness of a Rabin tree automaton to a finite Rabin game, and a source check of E. A. Emerson and C. S. Jutla, "The complexity of tree automata and logics of programs", *Proceedings of the 29th IEEE FOCS*, 1988, for the exact statement (proof prerequisite and source check; not yet stated)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): the remarks after the proof of Theorem 6.18, crediting the bound and the NP-completeness to Emerson and Jutla (1988).
