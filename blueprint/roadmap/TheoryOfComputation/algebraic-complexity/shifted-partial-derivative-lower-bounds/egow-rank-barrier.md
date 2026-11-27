# Efremenko–Garg–Oliveira–Wigderson: barriers for rank methods

A **rank method** for a tensor $T \in \mathbb{F}^{n} \otimes \mathbb{F}^{n} \otimes \mathbb{F}^{n}$ is a linear map $\Phi$ from the tensor space to a space of matrices with $\operatorname{rank}\Phi(a \otimes b \otimes c) \le r_0$ for all rank-one tensors; it certifies the tensor-rank lower bound $\operatorname{rank}\Phi(T)/r_0$, and rank methods for $d$-dimensional tensors are defined in the same way with rank-one tensors $a_1 \otimes \cdots \otimes a_d$. Over every sufficiently large field (of size polynomial in $n$ and $d$), no rank method certifies a tensor-rank lower bound above $2^d n^{\lfloor d/2 \rfloor}$ for any $d$-dimensional tensor of side $n$; in particular no rank method certifies a tensor-rank lower bound above $8n$ for any $3$-tensor in $(\mathbb{F}^n)^{\otimes 3}$. Likewise, no rank method (with simple polynomials the $d$-th powers of affine forms) certifies a Waring-rank lower bound above $(d+1)\binom{n + \lfloor d/2 \rfloor}{n}$ for any $n$-variate polynomial of degree $d$.

## Proof sketch

View $\Phi$ applied to a generic rank-one tensor (or $d$-th power) as a symbolic matrix whose entries are polynomials in the coefficients of the linear forms. Over a large enough field its symbolic rank equals the maximum rank of its evaluations, hence is at most $r_0$, and it factors as $KM$ through dimension $r' = 2^d r_0$ (tensor rank) or $(d+1) r_0$ (Waring rank) with homogeneous polynomial entries. For each of the $r'$ inner indices, the corresponding column of $K$ or row of $M$ has degree at most $\lfloor d/2 \rfloor$, so its coefficient vectors span a space of dimension $D \approx n^{\lfloor d/2 \rfloor}$. By linearity, every $\Phi(T)$ is a sum of a matrix with column space and a matrix with row space spanned by these $r' D$ vectors in total, so $\operatorname{rank}\Phi(T) \le r' D$ and the certified bound is at most $r' D / r_0$.

## Depends on

- [Tensor rank](../matrix-multiplication-exponent/tensor-rank.md)

## Sources

- K. Efremenko, A. Garg, R. Oliveira, A. Wigderson, "Barriers for rank methods in arithmetic complexity", ITCS (2018), arXiv:1710.09502.
