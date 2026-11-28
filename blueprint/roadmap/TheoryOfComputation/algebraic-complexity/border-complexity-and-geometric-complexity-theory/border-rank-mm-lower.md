# Landsberg–Ottaviani lower bound on the border rank of matrix multiplication

Let $\langle n, n, n \rangle \in \mathbb{C}^{n^2} \otimes \mathbb{C}^{n^2} \otimes \mathbb{C}^{n^2}$ be the matrix multiplication tensor and define its **border rank** as the least $r$ such that it is a limit of tensors of rank at most $r$. Then

$$
\underline{R}\bigl(\langle n, n, n \rangle\bigr) \ge 2n^2 - n.
$$

Earlier, Bürgisser and Ikenmeyer showed via highest weight vectors in the coordinate ring of secant varieties that GCT-type representation-theoretic obstructions give $\underline{R}(\langle n,n,n\rangle) \ge \frac{3}{2}n^2 - 2$.

## Proof sketch

Use a Koszul flattening: map the tensor to a linear map $\Lambda^{p}\mathbb{C}^{2p+1} \otimes \mathbb{C}^{n^2} \to \Lambda^{p+1}\mathbb{C}^{2p+1} \otimes \mathbb{C}^{n^2}$ after restricting one factor to a generic $(2p+1)$-dimensional quotient. Rank-one tensors map to maps of rank $\binom{2p}{p}$, while for matrix multiplication the image has rank at least $\binom{2p+1}{p}(n^2 - \text{small})$; the ratio gives the bound for the optimal $p = n - 1$.

## Depends on

- [Matrix multiplication tensor](../matrix-multiplication-exponent/matrix-multiplication-tensor.md)
- [Tensor rank](../matrix-multiplication-exponent/tensor-rank.md)

## Proof depends on

- [Efremenko–Garg–Oliveira–Wigderson: barriers for rank methods](../shifted-partial-derivative-lower-bounds/egow-rank-barrier.md)

## Sources

- J. M. Landsberg, G. Ottaviani, "New lower bounds for the border rank of matrix multiplication", Theory of Computing 11 (2015) 285-298, arXiv:1112.6007.
- P. Bürgisser, C. Ikenmeyer, "Explicit lower bounds via geometric complexity theory", STOC (2013), arXiv:1210.8368.
