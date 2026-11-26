# Homogeneous depth-five circuits for IMM need n^{Ω(√n)} gates

Over every field of characteristic zero and for all sufficiently large $n$ (explicitly $n\ge e^{29200}$), every syntactically homogeneous $\Sigma\Pi\Sigma\Pi\Sigma$ circuit computing $\mathrm{IMM}_{n,n}$ as a formal polynomial has at least $n^{\sqrt n/400}$ lower product, middle sum and upper product gates.

## Proof sketch

A homogeneous depth-five circuit with $S_1$ lower and $S_3$ upper products has rank measure at most $2S_3\max(S_1,1)\,D\,n^{-c\sqrt n}$ for suitable parameters, by the product rule and degree-weight estimates, while $\mathrm{IMM}_{n,n}$ has rank measure at least $De^{-C\sqrt n}$ under a balanced layer schedule; comparing gives the bound.

## Depends on

- [Homogeneous depth-five (ΣΠΣΠΣ) circuits](homogeneous-depth-five-circuits.md)
- [A rank measure from differentiation and multiplication](depth-five-rank-measure.md)

## Proof depends on

- [The rank measure of iterated matrix multiplication](rank-measure-of-iterated-matrix-multiplication.md)
- [A rank lower bound from two trace moments](../../../LinearAlgebra/matrix-algebra/rank-bounds-for-complexity/rank-lower-bound-from-trace-moments.md)

## Sources

- OpenAI, "Homogeneous Depth-Five Lower Bounds for Iterated Matrix Multiplication", Preprint, 2026.
