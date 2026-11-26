# Purifications attaining the overlap bound

Let `p` and `q` be probability vectors on a finite type `X` (nonnegative,
each summing to `1`). There are amplitude arrays `A B : X → X → ℂ`, with
environment a copy of `X`, such that the rows of `A` and `B` have squared
norms `p x` and `q x`, distinct rows of each array are orthogonal, both
arrays have total squared norm `1`, and `|∑ x, ∑ e, conj (A x e) * B x e| =
∑ x, √(p x * q x)`, the Bhattacharyya coefficient of `p` and `q`.

The arrays are the canonical purifications `∑ x, √(p x) |x⟩|x⟩` and `∑ x,
√(q x) |x⟩|x⟩` of the density states `diag p` and `diag q`: unit vectors
with exactly these reduced states, whose overlap attains the Bhattacharyya
coefficient.
