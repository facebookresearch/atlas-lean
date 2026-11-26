# Long i-sequences detect the winner of a positional play

Let $\pi$ be the play of a [parity game](../parity-games/parity-game.md) with $n$ vertices obtained when both players follow positional strategies.
If Eve wins, then prefixes of $\pi$ contain [$i$-sequences](i-sequences-and-records.md) for arbitrarily large $i$; if Adam wins, then no prefix of $\pi$
contains a $(\lceil \log_2 n \rceil + 1)$-sequence. For the second claim, let $i = \lceil \log_2 n \rceil + 1$ and $n \ge 2$ (for $n = 1$ a play that Adam wins has no even
priority, so no $i$-sequence with $i \ge 1$). The first $2^i - 1 \ge 2n - 1 > n$ indices of an $i$-sequence all carry even priorities, so two of them sit on the same
vertex; by inner domination the largest priority on the cycle between them is one of these even indexed priorities, and the positional play repeats
that cycle forever, so Eve would win.

The cited chapter states the second claim for $\lceil \log_2 n \rceil$-sequences, but $2^{\lceil \log_2 n \rceil}$ indices need not repeat a vertex: with two
vertices of priorities $2$ and $1$ and the play $2, 1, 1, \dots$, which Adam wins, the prefix $2, 1$ is a $1$-sequence. Calude, Jain, Khoussainov, Li and
Stephan likewise track sequences of length at least $2n + 1$.

## Depends on

- [i-sequences and records](i-sequences-and-records.md)
- [Parity game](../parity-games/parity-game.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.4, Lemma 2.9 (completeness for the separating automaton) with its proof.
- C. S. Calude, S. Jain, B. Khoussainov, W. Li and F. Stephan, "Deciding parity games in quasipolynomial time", *Proceedings of the 49th ACM STOC*, 2017 (numbering of the authors' preprint, <http://www.cmap.polytechnique.fr/~gaubert/COURSM2/PARITYGAMES/paritygame.pdf>): Section 2, the definition of winning statistics, which tracks sequences of length at least $2n + 1$ through $(\lceil \log n \rceil + 2)$-sequences of a variant of $i$-sequences.
