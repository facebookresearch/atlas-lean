# Iterated matrix multiplication and word polynomials

For $n,d\ge1$, the *iterated matrix multiplication polynomial* $\mathrm{IMM}_{n,d}$ is the $(1,1)$ entry of the product $X^{(1)}X^{(2)}\cdots X^{(d)}$ of $d$ generic $n\times n$ matrices with disjoint sets of variables; it is set-multilinear in the $d$ blocks of matrix entries and computable by an ABP of width $n$ and length $d$. For a word $w\in\mathbb{Z}^d$, the *word polynomial* $P_w$ is a set-multilinear polynomial on blocks of sizes $2^{|w_i|}$ whose partial-derivative matrix $M_w(P_w)$ has full rank; $P_w$ is a set-multilinear projection of $\mathrm{IMM}_{n,d}$ when $2^{\max|w_i|}\le n$.

## Depends on

- [Set-multilinear polynomials and formulas](set-multilinear-polynomials-and-formulas.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021.
