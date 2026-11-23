# Stability of zero-dimensional persistence

Let $d_1, d_2 \colon X \times X \to \mathbb{R}$ be two dissimilarities on the same set $X$ and let
$\eta \ge 0$. If $|d_1(x, y) - d_2(x, y)| \le \eta$ for all $x, y \in X$, then their cluster
functors are $\eta$-interleaved: an $r$-cluster for $d_1$ lies in an $(r + \eta)$-cluster for
$d_2$ and conversely, and the two round trips are the structure maps over $2\eta$ (interleavings
as in Chazal, de Silva, Glisse and Oudot, arXiv:1207.3674, §3.2; the inclusions are the chain
argument of Carlsson and Mémoli, JMLR 11 (2010), Lemma 15).

## Background

- [Algebraic stability theorem](is-matching-of-interleaving.md): for finite $X$, after
  linearization (the free vector space on the clusters at each scale, a pointwise
  finite-dimensional persistence module), this interleaving is the hypothesis of the
  algebraic stability theorem, which then bounds the bottleneck distance between the
  zero-dimensional barcodes.
