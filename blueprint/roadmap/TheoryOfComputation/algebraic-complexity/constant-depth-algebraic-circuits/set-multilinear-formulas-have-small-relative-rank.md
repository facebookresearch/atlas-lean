# Small set-multilinear formulas have small relative rank

Let $\alpha=1/\sqrt2$, let $d,k,\Delta\ge1$ be integers with $k\ge10d$, and let $w$ be a word of length $d$ each of whose letters is $\lfloor\alpha k\rfloor$ or $-k$, in any order. Every syntactically set-multilinear formula of product-depth at most $\Delta$ with at most $s$ nodes, set-multilinear on the blocks of $w$, computes a polynomial $f$ with

$$
\mathrm{relrk}_w(f)\le s\cdot 2^{-k\,d^{1/(2^\Delta-1)}/20} .
$$

The lower bound for iterated matrix multiplication applies this to the $k$-unbiased word built greedily: $w_{i+1}=\lfloor\alpha k\rfloor$ if $w_1+\dots+w_i\le0$ and $w_{i+1}=-k$ otherwise.

## Proof sketch

Induct on $\Delta$. For $\Delta=1$ each product is a product of $d$ linear forms, each of relative rank at most $2^{-|w_j|/2}\le2^{-k/4}$ by imbalance, so multiplicativity and subadditivity give $s\,2^{-kd/4}$. For the step, split the top sum's children according to whether some factor has degree at least $T_\Delta=d^{(2^\Delta-1)/(2^{\Delta+1}-1)}$: such a factor has small relative rank by induction; otherwise there are more than $d/T_\Delta$ factors, and since $\alpha$ is irrational with $|a\alpha-b|\ge1/(4|a\alpha|+2)$ for all integers $a,b$, each factor's subword sum has absolute value at least $k/(10T_\Delta)$, so multiplicativity and the imbalance bound give the claimed estimate.

## Depends on

- [Relative rank of set-multilinear polynomials](relative-rank-of-set-multilinear-polynomials.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021; full version, Electronic Colloquium on Computational Complexity TR21-081, revision 1, Claims 16 and 17 (in the proof of Lemma 15).
