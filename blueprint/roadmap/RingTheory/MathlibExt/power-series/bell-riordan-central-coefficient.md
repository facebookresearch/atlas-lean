---
article_id: af_ad63584708627688d6ed3fa4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bell_riordan_central_coefficient
---

# Bell Riordan Central Coefficient

Central coefficients of Bell-subgroup Riordan matrices: for the Bell matrix
`(g(X), X*g(X))`, the entry in row `2*n` and column `n` equals `(n+1)`
times the degree-`(n+1)` coefficient of the compositional inverse `u` of
`X / g(X)`.

The paper's `[x^n] (1/x) u(x)` is rendered as `coeff (n+1) u`, and
`T_{2n,n} = [x^{2n}] g*(X*g)^n` follows the paper's proof.

## Depends on

- [Bell Matrix](../../../NumberTheory/MathlibExt/part-03/bell-matrix/bell-matrix.md)
- [Entry](../../../NumberTheory/MathlibExt/part-03/bell-matrix/entry.md)

## Proof depends on

- [Fps lagrange burmann coeff'](lagrange-burmann-coefficient/fps-lagrange-burmann-coeff.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.PowerSeries.BellRiordanCentralCoefficient](../../../../sources/v2/MathlibExt.md)
- Paul Barry, "On the Central Coefficients of Bell Matrices," Journal of Integer Sequences 14 (2011), Article 11.4.3, Theorem `laterthm`, lines 167-169, <https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry3/barry132.tex>.
