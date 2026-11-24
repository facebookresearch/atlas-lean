# Valiant-Vazirani: SAT reduces to UniqueSAT

There are a polynomial $p$ with
natural-number coefficients and a polynomial-time computable function $R$ from pairs of
bitstrings to bitstrings such that, for every bitstring $x$ of length $n$: if $x$ is not in SAT,
then for every bitstring $r$ of length $p(n)$ the bitstring $R(x, r)$ is in neither SAT nor
UniqueSAT; and if $x$ is in SAT, then the number $N$ of bitstrings $r$ of length $p(n)$ for which
$R(x, r)$ is in UniqueSAT satisfies $8(n + 1) N \ge 2^{p(n)}$.

Here SAT and UniqueSAT are the bitstring decision problems for CNF formulas with the variable
count given in unary.

## Sources

- L. G. Valiant and V. V. Vazirani, "NP is as easy as detecting unique solutions", Theoretical Computer Science 47 (1986), 85-93 (STOC 1985).
