# Büchi–Landweber theorem

Muller games are determined with finite memory, and they are solvable: in every game whose condition is a
[Muller objective](muller-rabin-and-streett-objectives.md) $\mathrm{Muller}(\mathcal{F})$ over $d$ colors, from every vertex one of the
two players has a winning strategy using a memory structure of size at most $d!$, and for finite games the winning regions
and such strategies are computable, in time $O(d m (d n)^{d - 1})$ and space $O(d m)$ for a game with $n$ vertices and $m$
edges (Büchi and Landweber, who stated it for games on finite graphs; the memory comes from latest appearance records,
following Gurevich and Harrington). This solves Church's synthesis problem for specifications given by automata on infinite
words, after the specification is made deterministic.

## Depends on

- [Muller, Rabin and Streett objectives](muller-rabin-and-streett-objectives.md)
- [Arenas, strategies and memory structures](arenas-strategies-and-memory-structures.md)

## Proof depends on

- [Attractor](../parity-games/attractor.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 3 (N. Fijalkow and F. Horn, "Regular games"): Theorem 3.1, Lemmas 3.2 and 3.3 (McNaughton's recursive algorithm) and Remark 3.1 (the results extend to infinite games).
- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Theorem 6.16 (effective determinacy of finite-state games, credited to Büchi and Landweber) and the discussion after it of Church's problem and of the original Muller-condition proof.
