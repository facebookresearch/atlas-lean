# Records witness i-sequences

Let $(b_\ell, \dots, b_0)$ be the [record](i-sequences-and-records.md) of Eve after a prefix of a play of a parity game with $n$ positions. The update keeps these invariants:

- $b_i \ne 0$ exactly when the record tracks an $i$-sequence for Eve in the prefix, and $b_i$ is then the largest priority visited at or after the end of that sequence;
- if $b_i, b_j \ne 0$ and $i < j$, then $b_i \le b_j$, and the tracked $i$-sequence starts only after a position of priority $b_j$ that is visited at or after the end of the tracked $j$-sequence.

In particular, if Eve is declared the winner, the prefix contains an $\ell$-sequence for Eve with $2^\ell > 2n$.

Conversely, Eve is eventually declared the winner on every infinite play whose largest priority $c$ seen infinitely often is even. After the last visit
of a priority above $c$, the number
$$\sum \{ 2^k : b_k \text{ is even and } b_k \ge c \}$$
strictly increases between any two consecutive visits to $c$. It is bounded while Eve is not declared the winner.

## Depends on

- [i-sequences and records](i-sequences-and-records.md)

## Sources

- C. S. Calude, S. Jain, B. Khoussainov, W. Li and F. Stephan, "Deciding parity games in quasipolynomial time", *Proceedings of the 49th ACM STOC*, 2017 (numbering of the authors' preprint, <http://www.cmap.polytechnique.fr/~gaubert/COURSM2/PARITYGAMES/paritygame.pdf>): Section 2, the invariants of the winning statistics and the paragraph "Verification of the algorithm" (preservation of the invariants), and Claim 4 with its proof. The proof of Claim 4 uses only that the largest priority seen infinitely often has the player's parity.
