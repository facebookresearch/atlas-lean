# Relative rank of set-multilinear polynomials

Let $f$ be set-multilinear on blocks $X_1,\dots,X_d$ with $|X_i|=2^{|w_i|}$ for a *word* $w=(w_1,\dots,w_d)\in\mathbb{Z}^d$. Split the blocks into positive ones $P=\{i:w_i>0\}$ and negative ones $N=\{i:w_i<0\}$. The *partial-derivative matrix* $M_w(f)$ has rows indexed by set-multilinear monomials on $P$ and columns by those on $N$, with entries the coefficients of $f$. The *relative rank* is $\mathrm{relrk}_w(f)=\operatorname{rank}M_w(f)\big/\sqrt{2^{\sum_{i\in P}|w_i|}\,2^{\sum_{i\in N}|w_i|}}\le1$.

## Depends on

- [Set-multilinear polynomials and formulas](set-multilinear-polynomials-and-formulas.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021.
