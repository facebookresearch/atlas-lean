# Induced class function

For a subgroup `H` of a finite group `G`, a field `K` in which
the order of `H` is invertible (the instance argument `[NeZero (Nat.card H : K)]`) and
`φ : G → K`, the normalized Frobenius sum
`induced H φ g = |H|⁻¹ * ∑ x : G, [x⁻¹ * g * x ∈ H] * φ (x⁻¹ * g * x)`. It uses only the
values of `φ` on `H`. For `K = ℂ` and `φ` restricting on `H` to the character of a complex
representation of `H`, it is the character of the induced representation of `G`.
