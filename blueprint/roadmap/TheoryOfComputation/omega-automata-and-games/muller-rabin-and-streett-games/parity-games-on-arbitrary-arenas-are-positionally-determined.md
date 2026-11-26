# Parity games on arbitrary arenas are positionally determined

Let $G$ be a parity game on an arena with an arbitrary, possibly infinite, set of vertices, with finitely many priorities,
where a play is won by Eve when the largest priority occurring infinitely often is even. From every vertex, one of the two
players has a positional winning strategy (Emerson and Jutla; Mostowski). This extends the
[positional determinacy of finite parity games](../parity-games/finite-parity-games-are-positionally-determined.md) and is
the determinacy result that complementation of tree automata on infinite trees uses, where the arenas are infinite.

The source states the result for the Rabin chain condition given by a chain $E_1 \subset F_1 \subset \dots \subset E_n \subset F_n$
of sets of vertices, under which a play is won when for some $k$ it visits $F_k$ infinitely often and $E_k$ only finitely
often; with $F_0 = \emptyset$, indexing the vertices in $E_i \setminus F_{i-1}$ by $2i - 1$, those in $F_i \setminus E_i$ by $2i$ and those outside
$F_n$ by $2n + 1$ makes this the parity condition with the least priority seen infinitely often deciding the winner, and replacing each
priority $p$ by $2n + 2 - p$, which reverses the order and keeps the parity, turns it into the largest-priority convention used here.

## Depends on

- [Parity game](../parity-games/parity-game.md)
- [Positional strategy in a parity game](../parity-games/positional-strategy.md)

## Proof depends on

- [Attractor](../parity-games/attractor.md)
- [Reversing priorities exchanges the min-parity and max-parity conditions](../parity-condition-on-infinite-sequences/reversing-priorities-exchanges-min-parity-and.md)

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Theorem 6.13 (memoryless determinacy of Rabin chain games), Lemma 6.14 (attractor lemma) and the proof of Theorem 6.13 by transfinite attractor constructions; Definition 6.4 for the Rabin chain and parity conditions.
