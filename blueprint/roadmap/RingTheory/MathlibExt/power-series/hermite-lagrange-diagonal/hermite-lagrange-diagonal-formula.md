---
article_id: af_f08a496b1efe5a5bce7022c4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.LagrangeInversion.hermite_lagrange_diagonal_formula
---

# Hermite lagrange diagonal formula

Hermite's distinct diagonal/reversion form: the `n`-th coefficient of
`F * phi ^ n` equals the `n`-th coefficient of the diagonal generating series `G`, where `w` is
the reverted series (`w = X * phi(w)`) and `(1 - X * phi'(w)) * G = F(w)`.

This contrasts with the derivative-coefficient form in
`WantedExt/RingTheory/PowerSeries/LagrangeBurmannCoefficientWanted.lean`, which
extracts the coefficient via an explicit derivative factor; here the derivative
is instead absorbed into the defining equation for `G`. No definitions are
duplicated.

Reference: Bakir Farhi, "Some Applications of the Lagrange Inversion Formula
for the k-Fibonacci Numbers", Journal of Integer Sequences 27 (2024),
Hermite corollary and derivation lines 205-240.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.RingTheory.PowerSeries.HermiteLagrangeDiagonal](../../../../../sources/v2/MathlibExt.md)
- https://cs.uwaterloo.ca/journals/JIS/VOL27/Farhi/farhi35.tex Complete-source SHA-256: ade74bb31bb7d561d2e57515f2125656c2c0a2482237711179e3589bb4b26f27 Normalized statement lines 205-210 SHA-256: 6e89d7158aae443fa6bf9907f922bc8b116a023093496193a6d016f01de94f7b Normalized lines 205-240 SHA-256: 06cba9424deb1a7b852172a86dbc1088947b1225aad87d0577386d59fa3aed58
