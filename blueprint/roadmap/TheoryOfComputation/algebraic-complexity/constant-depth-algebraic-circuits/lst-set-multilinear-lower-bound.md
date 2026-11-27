# LST lower bound for set-multilinear formulas computing IMM

Let $\alpha=1/\sqrt2$, let $d,k,\Delta\ge1$ with $k\ge10d$, and let $w$ be the $k$-unbiased word of length $d$ with letters $\lfloor\alpha k\rfloor$ and $-k$ built greedily. Every syntactically set-multilinear formula of product-depth at most $\Delta$ computing the word polynomial $P_w$ has at least

$$
2^{k\left(d^{1/(2^\Delta-1)}/20-1/2\right)}
$$

nodes. Consequently, for $n\ge2^{10d+1}$, every set-multilinear circuit of product-depth at most $\Delta$ computing $\mathrm{IMM}_{n,d}$ has a size $s$ with $s^{2\Delta}\ge2^{\lfloor\log_2n\rfloor\left(d^{1/(2^\Delta-1)}/20-1/2\right)}$; in particular $s\ge n^{\Omega(d^{1/(2^\Delta-1)})/\Delta}$ whenever $d^{1/(2^\Delta-1)}\ge20$.

## Proof sketch

$M_w(P_w)$ has full rank and $|w_1+\dots+w_d|\le k$, so $\mathrm{relrk}_w(P_w)\ge2^{-k/2}$, while a set-multilinear formula of product-depth at most $\Delta$ with $s$ nodes computes a polynomial of relative rank at most $s\,2^{-k\,d^{1/(2^\Delta-1)}/20}$; comparing the two gives the bound. For $\mathrm{IMM}_{n,d}$ take $k=\lfloor\log_2n\rfloor$, obtain $P_w$ from $\mathrm{IMM}_{n,d}$ by a set-multilinear substitution, and unfold a set-multilinear circuit of size $s$ and product-depth $\Delta$ into a set-multilinear formula of product-depth $\Delta$ and size at most $s^{2\Delta}$. When $d^{1/(2^\Delta-1)}\ge20$ the exponent is at least $\lfloor\log_2n\rfloor\,d^{1/(2^\Delta-1)}/40$; for small $d$ the bound is below $1$ (for $d=1$, $\mathrm{IMM}_{n,1}$ is a single variable).

## Depends on

- [Iterated matrix multiplication and word polynomials](iterated-matrix-multiplication-polynomial.md)
- [Relative rank of set-multilinear polynomials](relative-rank-of-set-multilinear-polynomials.md)

## Proof depends on

- [Small set-multilinear formulas have small relative rank](set-multilinear-formulas-have-small-relative-rank.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021; full version, Electronic Colloquium on Computational Complexity TR21-081, revision 1, Lemma 8 and Lemma 15 with its proof.
