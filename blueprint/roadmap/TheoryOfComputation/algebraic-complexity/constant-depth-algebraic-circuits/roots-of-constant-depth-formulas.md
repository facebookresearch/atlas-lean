# Roots of constant product-depth formulas have small formulas

Over a field of characteristic zero, let $x=(x_1,\dots,x_n)$, let $P(x,y)\neq0$ have total degree at most $D$ and be computed by an unbounded fan-in circuit of size $s$ and product-depth $\Delta$, and let $f(x)$ be a polynomial with $P(x,f(x))=0$. Then $f$ is computed by an unbounded fan-in circuit of size $\mathrm{poly}(s,D,n)$ and product-depth $\Delta+O(1)$, with an absolute polynomial and an absolute constant. In particular, if $P$ has a formula of size $s$ and product-depth $\Delta$, then $f$ has a formula of product-depth $\Delta+O(1)$ and size $(sDn)^{O(\Delta+1)}$, which is polynomial for constant $\Delta$.

## Proof sketch

Since $P(x,f(x))=0$, the polynomial $y-f(x)$ is a factor of $P$, so $f$ is obtained by setting $y=0$ in a factor of $P$. After reducing to a squarefree polynomial and a generic shift, each factor is a product of power series roots $\varphi$ with $\varphi(0)=0$ and $\partial_yP(0,0)\ne0$, and Furstenberg's non-iterative formula $\varphi=\sum_{m\ge1}[y^{m-1}]\bigl(\partial_yP\cdot(y-P)^m\bigr)$ (after normalizing $\partial_yP(0,0)=1$) needs only the terms $m\le2\deg f$ to determine the homogeneous parts of $\varphi$ up to degree $\deg f$. Coefficient extraction and homogeneous-part extraction are done by interpolation, adding constant depth; a circuit of product-depth $\Delta'$ and size $S$ unfolds into a formula of size $S^{O(\Delta'+1)}$.

## Depends on

- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](unbounded-fan-in-formulas-and-product-depth.md)

## Sources

- Somnath Bhattacharjee, Mrinal Kumar, Shanthanu S. Rai, Varun Ramanathan, Ramprasad Saptharishi, Shubhangi Saraf, "Closure under factorization from a result of Furstenberg", 58th Annual ACM Symposium on Theory of Computing (STOC 2026), 2026; arXiv:2506.23214, Theorem 1.1, Corollary 3.3 and Theorem 4.1.
- Chi-Ning Chou, Mrinal Kumar, Noam Solomon, "Closure Results for Polynomial Factorization", Theory of Computing, 2019 (the earlier bounded-degree version).
