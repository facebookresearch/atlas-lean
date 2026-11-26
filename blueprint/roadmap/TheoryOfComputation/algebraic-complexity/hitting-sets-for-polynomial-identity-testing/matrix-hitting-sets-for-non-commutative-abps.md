# Quasipolynomial matrix hitting sets for non-commutative ABPs

Over a field of characteristic zero, there is an explicit set of $n$-tuples of $(d+1)\times(d+1)$ matrices, of size $(ndW)^{O(\log d)}$, such that every nonzero non-commutative polynomial of degree $d$ in $n$ variables computed by a homogeneous layered ABP of width at most $W$ is nonzero at one of the tuples.

## Proof sketch

Forbes–Shpilka reduction: substituting upper-triangular shift matrices $x_i\mapsto\sum_{k}y_{k,i}E_{k,k+1}$ turns the non-commutative ABP into a commutative ROABP in $d$ new variables with width $W$ and layer degree $n-1$; apply a hitting set for ROABPs in known order.

## Depends on

- [Non-commutative arithmetic circuits and algebraic branching programs](../algebraic-circuit-lower-bound-methods/non-commutative-circuits-and-abps.md)
- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)
- [Read-once oblivious algebraic branching programs](../algebraic-circuit-lower-bound-methods/read-once-oblivious-abps.md)

## Proof depends on

- [Quasipolynomial hitting sets for ROABPs in unknown order](hitting-sets-for-roabps-in-unknown-order.md)

## Sources

- Michael A. Forbes, Amir Shpilka, "Quasipolynomial-Time Identity Testing of Non-commutative and Read-Once Oblivious Algebraic Branching Programs", 54th Annual IEEE Symposium on Foundations of Computer Science (FOCS), 2013.
- Manindra Agrawal, Rohit Gurjar, Arpita Korwar, Nitin Saxena, "Hitting-Sets for ROABP and Sum of Set-Multilinear Circuits", SIAM Journal on Computing, 2015.
