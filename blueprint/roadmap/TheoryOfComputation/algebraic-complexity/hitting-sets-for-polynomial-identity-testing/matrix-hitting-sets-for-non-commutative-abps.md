# Quasipolynomial matrix hitting sets for non-commutative ABPs

Over a field of characteristic zero, there is an explicit set of $n$-tuples of $(d+1)\times(d+1)$ matrices, of size $(ndW)^{O(\log d)}$, such that every nonzero non-commutative polynomial of degree $d$ in $n$ variables computed by a homogeneous layered ABP of width at most $W$ is nonzero at one of the tuples.

## Proof sketch

Substitute strictly upper-triangular $(d+1)\times(d+1)$ matrices $x_i\mapsto\sum_{k=1}^{d}y_k^{\,i-1}E_{k,k+1}$: the $(1,d+1)$ entry of $f$ evaluated there is $\sum_w\mathrm{coeff}_w(f)\prod_ky_k^{\,i_k-1}$ over words $w=x_{i_1}\cdots x_{i_d}$, which is nonzero iff $f$ is and is computed by a commutative ROABP in $y_1,\dots,y_d$ of width $W$ and individual degree at most $n-1$; apply a hitting set for ROABPs. (Forbes and Shpilka use the analogous reduction to set-multilinear ABPs.)

## Depends on

- [Non-commutative arithmetic circuits and algebraic branching programs](../algebraic-circuit-lower-bound-methods/non-commutative-circuits-and-abps.md)
- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)
- [Read-once oblivious algebraic branching programs](../algebraic-circuit-lower-bound-methods/read-once-oblivious-abps.md)

## Proof depends on

- [Quasipolynomial hitting sets for ROABPs in unknown order](hitting-sets-for-roabps-in-unknown-order.md)

## Sources

- Michael A. Forbes, Amir Shpilka, "Quasipolynomial-Time Identity Testing of Non-commutative and Read-Once Oblivious Algebraic Branching Programs", 54th Annual IEEE Symposium on Foundations of Computer Science (FOCS), 2013 (arXiv:1209.2408), Corollary 4.7 (over fields with at least $(2(d+1)^5nW^4)^2$ elements, size at most $(2(d+1)^4n^2W^3)^{\lceil\log_2d\rceil+1}$).
- Manindra Agrawal, Rohit Gurjar, Arpita Korwar, Nitin Saxena, "Hitting-Sets for ROABP and Sum of Set-Multilinear Circuits", SIAM Journal on Computing, 2015.
