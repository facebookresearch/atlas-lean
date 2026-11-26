# Quasipolynomial hitting sets for ROABPs in unknown order

Over a field of characteristic zero, there is an explicit set $H\subseteq F^n$ of size $(n\delta w)^{O(\log n)}$, independent of the variable order, that contains a non-root of every nonzero $n$-variate polynomial computed by a width-$w$ ROABP (in some order) whose layer entries have degree at most $\delta$. The construction combines the variables in $\lceil\log_2n\rceil$ levels, each using a basis-isolating weight assignment modulo a prime $p\le2(2n^2w^8+\delta+1)$.

## Proof sketch

The coefficient vectors of an ROABP span a space of dimension at most $w^2$ for every segment; a weight assignment isolating a basis of this span (a 'basis isolating weight') exists among few candidates, and substituting $x_i\mapsto t^{\mathrm{wt}(i)}$ reduces the number of variables while preserving nonzeroness. Recursion halves the number of variable groups per level.

## Depends on

- [Read-once oblivious algebraic branching programs](../algebraic-circuit-lower-bound-methods/read-once-oblivious-abps.md)
- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)

## Sources

- Manindra Agrawal, Rohit Gurjar, Arpita Korwar, Nitin Saxena, "Hitting-Sets for ROABP and Sum of Set-Multilinear Circuits", SIAM Journal on Computing, 2015.
