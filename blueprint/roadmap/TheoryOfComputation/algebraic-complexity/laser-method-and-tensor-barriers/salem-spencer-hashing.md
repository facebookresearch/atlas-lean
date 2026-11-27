# Coppersmith–Winograd hashing with progression-free sets

Let $M$ be a positive integer and $B \subseteq \mathbb{Z}_M$ a set without nontrivial solutions to $a + b \equiv 2c \pmod M$. For a tensor power $T^{\otimes N}$ whose block indices are vectors in $\{0, 1, 2\}^N$ satisfying $I + J + K = 2 \cdot \mathbf{1}$, assume $M$ odd, choose independent uniformly random $w_X, w_Y \in \mathbb{Z}_M$ and $w \in \mathbb{Z}_M^N$, and define hashes $h_X(I) = w_X + \langle w, I \rangle$, $h_Y(J) = w_Y + \langle w, J \rangle$, $h_Z(K) = \frac{1}{2}\bigl(w_X + w_Y + 2\langle w, \mathbf{1}\rangle - \langle w, K\rangle\bigr) \bmod M$, with $\frac12$ the inverse of $2$ modulo $M$. Zeroing out all block variables whose hash is outside $B$ leaves only block triples $(I, J, K)$ with $h_X(I) = h_Y(J) = h_Z(K)$, and for every surviving block triple the probability that it survives is $|B|/M^2$. Taking $B$ of size $M^{1 - o(1)}$ (Behrend), after a further greedy pruning one obtains, in expectation, a direct sum of $M^{-o(1)}$ times the expected number of surviving independent block triples.

## Proof sketch

If $(I,J,K)$ is a block triple, then $h_X(I) + h_Y(J) = 2h_Z(K)$ by the constraint $I + J + K = 2\cdot\mathbf{1}$, so all three hashes lie in $B$ only if they are equal. For a block triple, $h_X(I)$ and $h_Y(J)$ are independent and uniform because the offsets $w_X,w_Y$ are, so the triple survives with probability $\sum_{b\in B}\Pr[h_X(I)=h_Y(J)=b]=|B|/M^2$; a single shared offset would make all three hashes of the triple $I=J=0$, $K=2\cdot\mathbf{1}$ equal to that offset, giving survival probability $|B|/M$. Remaining collisions (two triples sharing an $X$-block) are removed by zeroing out one of them, which keeps a constant fraction in expectation when the number of blocks per hash value is balanced.

## Depends on

- [The value of a tensor in the laser method](tensor-value.md)

## Proof depends on

- [Behrend's lemma: some sphere contains many lattice points of a cube](../../../Combinatorics/additive-combinatorics/progressions-dense-sets/bounds-for-roth-numbers/behrend-large-sphere.md)

## Sources

- D. Coppersmith, S. Winograd, "Matrix multiplication via arithmetic progressions", Journal of Symbolic Computation 9 (1990) 251-280.
- R. Salem, D. C. Spencer, "On sets of integers which contain no three terms in arithmetical progression", Proceedings of the National Academy of Sciences 28 (1942) 561-563.
- F. A. Behrend, "On sets of integers which contain no three terms in arithmetical progression", Proceedings of the National Academy of Sciences 32 (1946) 331-332.
