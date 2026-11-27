# Parity games are solvable in quasipolynomial time

There is an algorithm that decides which player wins a finite [parity game](../parity-games/parity-game.md) with $n$ positions and priorities
in $\{1, \dots, d\}$ from a given position in time $O(n^{\log d + 6})$, and that computes a positional winning strategy of
the winner in time $O(n^{\log d + 7} \log n)$ (Calude, Jain, Khoussainov, Li and Stephan). The algorithm reduces the
game to a reachability game on a product with Eve's *play summaries*, statistics of polylogarithmically many bits that record
witnesses of long runs of even domination. Read for Adam, the same statistics give a deterministic safety automaton that is a strong
$(n, d)$-separator with $n^{\log_2 d + O(1)}$ states, so the separating-automaton reduction also applies.

## Depends on

- [Parity game](../parity-games/parity-game.md)
- [Winning region of a parity game](../parity-games/winning-region.md)

## Proof depends on

- [The record automaton decides parity games](the-record-automaton-decides-parity-games.md)
- [Solving parity games with a separating automaton](solving-parity-games-with-a-separating-automaton.md)
- [Finite parity games are positionally determined](../parity-games/finite-parity-games-are-positionally-determined.md)

## Sources

- C. S. Calude, S. Jain, B. Khoussainov, W. Li and F. Stephan, "Deciding parity games in quasipolynomial time", *Proceedings of the 49th ACM STOC*, 2017 (numbering of the authors' preprint, <http://www.cmap.polytechnique.fr/~gaubert/COURSM2/PARITYGAMES/paritygame.pdf>): Theorem 7, with Theorem 1 (the alternating polylogarithmic-space algorithm) and Theorem 5 ($O(n^{c \log m})$); the source writes $m$ for the number of priorities and states $\log(m)$ in the exponent.
- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Theorem 2.5 (the original separating automaton, of size $n^{O(\log d)}$) and the proofs following it.
