# The record automaton decides parity games

Monitor the plays of a [parity game](../parity-games/parity-game.md) with $n$ vertices and priorities in $\{1, \dots, d\}$ with a [record](i-sequences-and-records.md)
$b_k, \dots, b_0$ of length $k + 1$, where $k = \lceil \log_2 n \rceil + 1$. Eve has a strategy ensuring that eventually $b_k \ne -$ if and only if she wins the
parity game. The record and its update rule form a deterministic automaton with at most $(d + 1)^{\lceil \log_2 n \rceil + 2} = n^{O(\log d)}$ states; it is an
$(n, d)$-[separating automaton](separating-automata-for-parity-games.md), with the states where $b_k \ne -$ accepting from then on. The cited chapter uses
$k = \lceil \log_2 n \rceil$, which is one too small: in the game with two vertices of priorities $2$ and $1$ and the play $2, 1, 1, \dots$, which Adam wins,
reading $2$ and then $1$ sets $b_1 = 1$ (see [long i-sequences detect the winner](i-sequences-detect-the-winner-of-positional-plays.md)).

## Depends on

- [Parity game](../parity-games/parity-game.md)
- [i-sequences and records](i-sequences-and-records.md)
- [Separating automata for parity games](separating-automata-for-parity-games.md)

## Proof depends on

- [Long i-sequences detect the winner of a positional play](i-sequences-detect-the-winner-of-positional-plays.md)
- [Records witness i-sequences](records-witness-i-sequences.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.4, Corollary 2.1 (correctness of the reduction for the separating automaton) and "The size of the automaton" that follows it, with Theorem 2.5.
- C. S. Calude, S. Jain, B. Khoussainov, W. Li and F. Stephan, "Deciding parity games in quasipolynomial time", *Proceedings of the 49th ACM STOC*, 2017 (numbering of the authors' preprint, <http://www.cmap.polytechnique.fr/~gaubert/COURSM2/PARITYGAMES/paritygame.pdf>): Section 2, the definition of winning statistics, which tracks sequences of length at least $2n + 1$ through $(\lceil \log n \rceil + 2)$-sequences of a variant of $i$-sequences.
