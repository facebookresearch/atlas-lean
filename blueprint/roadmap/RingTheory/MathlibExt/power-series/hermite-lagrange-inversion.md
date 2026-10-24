---
article_id: af_6a19b2ec008b0db1b671041c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.hermite_lagrange_inversion
---

# Hermite Lagrange Series

Hermite's form of Lagrange inversion as formal power series, cleared of
denominators: with `F = X / φ` (encoded by `F * φ = X`) and `ψ` its
compositional inverse, `X * (g ∘ ψ)` equals the coefficient series of
`g * φ^n` times `ψ * (F' ∘ ψ)`; i.e. `z (g∘ψ) / (ψ (F'∘ψ))` is the series
`∑ z^n [z^n](g φ^n)`. Distinct from the landed diagonal coefficient form,
which states a coefficient-level consequence rather than the series
identity itself.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.RingTheory.PowerSeries.HermiteLagrangeSeries](../../../../sources/v2/MathlibExt.md)
- Bakir Farhi, "Some Applications of the Lagrange Inversion Formula for the k-Fibonacci Numbers," Journal of Integer Sequences 27 (2024), Article 24.1.1, Corollary (Hermite, label t-her), lines 205–210, https://cs.uwaterloo.ca/journals/JIS/VOL27/Farhi/farhi35.tex
