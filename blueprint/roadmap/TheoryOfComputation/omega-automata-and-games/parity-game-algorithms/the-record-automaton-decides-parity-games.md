# The record automaton decides parity games

Monitor the plays of a [parity game](../parity-games/parity-game.md) with $n$ vertices and priorities in $\{1, \dots, d\}$ with a [record](i-sequences-and-records.md)
$b_{\lceil \log_2 n \rceil}, \dots, b_0$. Eve has a strategy ensuring that eventually $b_{\lceil \log_2 n \rceil} \ne -$ if and only if she wins the parity game. The
record and its update rule form a deterministic automaton with at most $(d + 1)^{\log_2 n + 1} = n^{O(\log d)}$ states; it is an
$(n, d)$-[separating automaton](separating-automata-for-parity-games.md), with the states where $b_{\lceil \log_2 n \rceil} \ne -$ accepting from then on.

## Depends on

- [i-sequences and records](i-sequences-and-records.md)
- [Separating automata for parity games](separating-automata-for-parity-games.md)

## Proof depends on

- [Long i-sequences detect the winner of a positional play](i-sequences-detect-the-winner-of-positional-plays.md)
- [Records witness i-sequences](records-witness-i-sequences.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.4, Corollary 2.1 (correctness of the reduction for the separating automaton) and "The size of the automaton" that follows it, with Theorem 2.5.
