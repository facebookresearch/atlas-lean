# Circuit complexity transfers between fields of the same characteristic

Let $P$ be a polynomial with integer coefficients. If (the image of) $P$ is computed within $S$ nodes by an arithmetic circuit over some field of characteristic $p$ (with $p=0$ allowed), then it is computed within $S$ nodes over every algebraically closed field of characteristic $p$. The same holds for approximation within $S$ nodes, with constants in $K[\varepsilon,\varepsilon^{-1}]$.

## Proof sketch

The circuit uses finitely many constants; they generate a finitely generated subring of a common extension of the prime field, which has a ring homomorphism to every algebraically closed field of the same characteristic (Nullstellensatz-type specialization). Mapping the constants along it preserves the computed integer polynomial.

## Depends on

- [Approximative (border) circuits and the class VPbar](border-complexity-and-vp-bar.md)

## Sources

- Anthropic, "VP ≠ VNP over every field", manuscript, 2026.
