# Yablonskii's formula upper bound for parity

Write $n=2^k+r$ with $0\le r\le 2^k$. The parity function $x_1\oplus\cdots\oplus x_n$ has a De Morgan formula with at most $2^k(2^k+3r)$ leaves. In particular every $n\ge 1$ admits a formula for parity with at most $\tfrac98 n^2$ leaves.

## Proof sketch

Split the bits into blocks of $2^{k-1}+\lfloor r/2\rfloor$ and $2^{k-1}+\lceil r/2\rceil$ bits and combine their parity formulas with $x\oplus y=(x\wedge\neg y)\vee(\neg x\wedge y)$, which doubles leaf counts; the bound is exactly additive along this recursion. The identity $9(2^k+r)^2-8\cdot 2^k(2^k+3r)=(2^k-3r)^2\ge 0$ gives the $\tfrac98 n^2$ bound.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [The parity language](../../../../complexity-classes/time-and-space-complexity-classes/parity-dec.md)

## Sources

- S. V. Yablonskii, "Realization of a linear function in the class of π-schemes", Doklady Akademii Nauk SSSR 94(5), 805–806, 1954.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
