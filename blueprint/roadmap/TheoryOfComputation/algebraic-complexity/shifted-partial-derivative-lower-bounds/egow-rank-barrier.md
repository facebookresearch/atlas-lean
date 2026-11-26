# Efremenko–Garg–Oliveira–Wigderson: barriers for rank methods

A **rank method** for a tensor $T \in \mathbb{F}^{n} \otimes \mathbb{F}^{n} \otimes \mathbb{F}^{n}$ is a linear map $\Phi$ from the tensor space to a space of matrices with $\operatorname{rank}\Phi(a \otimes b \otimes c) \le r_0$ for all rank-one tensors; it certifies the tensor-rank lower bound $\operatorname{rank}\Phi(T)/r_0$. For every field and every $n$, no rank method certifies a tensor-rank lower bound above $8n$ for any $3$-tensor in $(\mathbb{F}^n)^{\otimes 3}$. Analogous barriers hold for Waring rank of homogeneous polynomials and for partial-derivative flattenings.

## Proof sketch

A rank method is a tensor-valued linear map; the rank of $\Phi(T)$ is lower-semicontinuous, so the certified bound applies to border rank. Algebraic geometry of secant varieties shows that every tensor in $(\mathbb{F}^n)^{\otimes 3}$ lies close to a generic tensor of border rank at most about $8n$ in the image of any such map, specifically by producing an explicit degeneration that preserves $\operatorname{rank} \Phi$ while reducing border rank.

## Depends on

- [The dimension of shifted partial derivatives](shifted-partials-measure.md)
- [Tensor rank](../matrix-multiplication-exponent/tensor-rank.md)

## Sources

- K. Efremenko, A. Garg, R. Oliveira, A. Wigderson, "Barriers for rank methods in arithmetic complexity", ITCS (2018), arXiv:1710.09502.
