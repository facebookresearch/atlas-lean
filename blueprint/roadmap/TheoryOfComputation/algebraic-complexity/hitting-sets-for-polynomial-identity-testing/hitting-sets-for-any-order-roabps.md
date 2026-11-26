# Polynomial-size hitting sets for multilinear any-order ROABPs

Over a field of characteristic zero, there is an explicit set of points in $F^n$, of size polynomial in $n$ and $w$, that hits every nonzero multilinear $n$-variate polynomial computed by width-$w$ ROABPs in every variable order; more generally every nonzero multilinear polynomial of split rank at most $w$ across every subset of variables. Likewise, for variables in $n$ blocks of size $d$, an explicit set of size polynomial in $n,d,s$ times $(d+1)^{\lfloor\log_2s\rfloor+1}$ hits every nonzero set-multilinear depth-three circuit $\sum_{i=1}^{s}\prod_{j=1}^{n}\ell_{ij}$ (with $\ell_{ij}$ a linear form in block $j$).

## Proof sketch

Shift by the support-concentrating set so that some monomial of support at most $\log_2w$ survives; then a hitting set for polynomials with a low-support monomial (substituting few variables at a time along an explicit low-degree map) finishes. The set-multilinear case uses the block structure with individual degree $d$.

## Depends on

- [Read-once oblivious algebraic branching programs](../algebraic-circuit-lower-bound-methods/read-once-oblivious-abps.md)
- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)
- [Split rank of a polynomial across a variable partition](split-rank-across-a-partition.md)

## Proof depends on

- [Support-concentrating shifts for multilinear polynomials of small split rank](support-concentrating-shifts.md)

## Sources

- Amir Shpilka, "Polynomial-size hitting sets for multilinear any-order read-once algebraic branching programs and for set-multilinear depth-3 circuits with constant-size variable sets", Electronic Colloquium on Computational Complexity, 2026.
