# Long i-sequences detect the winner of a positional play

Let $\pi$ be a play of a [parity game](../parity-games/parity-game.md) with $n$ positions.

1. If the largest priority seen infinitely often in $\pi$ is even, then prefixes of $\pi$ contain [$i$-sequences for Eve](i-sequences-and-records.md) for every $i$. After the
   last visit of a larger priority, the visits to that priority form such sequences.
2. If a prefix of $\pi$ contains an $i$-sequence for Eve with $2^i > 2n$, then $\pi$ contains a loop with even maximum: a segment from a position back to the same position
   whose largest priority is even. Indeed, some position occurs twice among $a_1, \dots, a_{2^i}$, and the largest priority between these two occurrences is
   reached between some consecutive $a_k$ and $a_{k+1}$, so it is even.

In particular, if both players follow positional strategies and Adam wins, then no prefix of $\pi$ contains an $i$-sequence for Eve with $2^i > 2n$: such a loop would repeat forever.
The same holds for Adam with even and odd exchanged.

A threshold $2^i \ge n$ is not enough. With two positions of priorities $2$ and $1$ and the play $2, 1, 1, \dots$, which Adam wins, the prefix $2, 1$ is a
$1$-sequence. The cited chapter states this lemma for $\lceil \log_2 n \rceil$-sequences of its own variant, which is one too small for the same reason.

## Depends on

- [i-sequences and records](i-sequences-and-records.md)
- [Parity game](../parity-games/parity-game.md)

## Sources

- C. S. Calude, S. Jain, B. Khoussainov, W. Li and F. Stephan, "Deciding parity games in quasipolynomial time", *Proceedings of the 49th ACM STOC*, 2017 (numbering of the authors' preprint, <http://www.cmap.polytechnique.fr/~gaubert/COURSM2/PARITYGAMES/paritygame.pdf>): Section 2, Claim 2 (a player declared the winner has a loop whose maximum has that player's parity) with its proof.
- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.4, Lemma 2.9 with its proof, for the chapter's variant and threshold.
