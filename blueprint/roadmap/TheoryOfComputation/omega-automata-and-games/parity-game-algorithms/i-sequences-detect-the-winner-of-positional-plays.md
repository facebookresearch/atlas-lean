# Long i-sequences detect the winner of a positional play

Let $\pi$ be the play of a [parity game](../parity-games/parity-game.md) with $n$ vertices obtained when both players follow positional strategies.
If Eve wins, then prefixes of $\pi$ contain [$i$-sequences](i-sequences-and-records.md) for arbitrarily large $i$; if Adam wins, then no prefix of $\pi$
contains a $\lceil \log_2 n \rceil$-sequence. For the second claim, a $\lceil \log_2 n \rceil$-sequence has at least $n$ indices, so it repeats a vertex, and inner
domination makes the maximal priority on the cycle between the two occurrences even, which a positional winning strategy of Adam
forbids.

## Depends on

- [i-sequences and records](i-sequences-and-records.md)
- [Parity game](../parity-games/parity-game.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.4, Lemma 2.9 (completeness for the separating automaton) with its proof.
