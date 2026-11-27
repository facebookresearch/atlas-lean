# The record automaton decides parity games

Let $\mathcal{G}$ be a [parity game](../parity-games/parity-game.md) with $n$ positions, $m$ edges and priorities in $\{1, \dots, d\}$. Eve wins $\mathcal{G}$ from $v$ if and only if
she wins, from $v$ and the all-zero [record](i-sequences-and-records.md), the reachability game on the product of $\mathcal{G}$ with her record, where her goal is to be
declared the winner (Calude, Jain, Khoussainov, Li and Stephan).

- If Eve plays a positional winning strategy, every resulting play has an even largest priority seen infinitely often, so she is declared the winner.
- If Adam plays a positional winning strategy and Eve is declared the winner, the play contains a loop whose largest priority is even. Eve could then
  repeat that loop forever against the same strategy, a contradiction.

Before Eve is declared the winner, the record takes at most $(d + 1)^{\lceil \log_2 n \rceil + 2}$ values. The reachability game is therefore solved in time
$O(m \cdot (d + 1)^{\lceil \log_2 n \rceil + 2})$.

Read for Adam, the record gives a deterministic safety automaton over priorities that rejects as soon as Adam is declared the winner. This
automaton is a strong $(n, d)$-[separator](separating-automata-for-parity-games.md) with at most $1 + (d + 1)^{\lceil \log_2 n \rceil + 2}$ states (the top entry is $0$ before rejection, and one
rejecting sink suffices), which is $n^{\log_2 d + O(1)}$ when $d \le 2n$:

- it accepts every path of an $n$-vertex parity graph all of whose cycles have even maximum;
- it rejects every word whose largest priority seen infinitely often is odd.

Eve's own record is no separator: for the least $\ell$ with $2^\ell > 2n$, on $2^\ell$ copies of $2$ followed by $1$ forever, she is declared the winner although the word does not satisfy parity.

## Depends on

- [Parity game](../parity-games/parity-game.md)
- [i-sequences and records](i-sequences-and-records.md)
- [Separating automata for parity games](separating-automata-for-parity-games.md)

## Proof depends on

- [Long i-sequences detect the winner of a positional play](i-sequences-detect-the-winner-of-positional-plays.md)
- [Records witness i-sequences](records-witness-i-sequences.md)
- [Reachability and safety games are positionally determined and solvable in linear time](../muller-rabin-and-streett-games/reachability-and-safety-games.md)
- [Finite parity games are positionally determined](../parity-games/finite-parity-games-are-positionally-determined.md)

## Sources

- C. S. Calude, S. Jain, B. Khoussainov, W. Li and F. Stephan, "Deciding parity games in quasipolynomial time", *Proceedings of the 49th ACM STOC*, 2017 (numbering of the authors' preprint, <http://www.cmap.polytechnique.fr/~gaubert/COURSM2/PARITYGAMES/paritygame.pdf>): Section 2, Claims 2–4 with their proofs, and the proof of Theorem 6. The latter states the equivalence with the reachability game that keeps only one player's winning statistics, and with the dual survival game.
- W. Czerwiński, L. Daviaud, N. Fijalkow, M. Jurdziński, R. Lazić and P. Parys, "Universal trees grow inside separating automata: quasi-polynomial lower bounds for parity games", *Proceedings of the 30th ACM-SIAM SODA*, 2019, arXiv:1807.10546v2: Section 4.2, Theorem 4.2 (play summaries with the roles of the players swapped give deterministic safety automata that are strong $(n, d)$-separators of size $n^{\lg d + O(1)}$).
