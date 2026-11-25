# The overlap bound is attained

Let `p` and `q` be nonnegative real functions on a finite type `X`. There
are amplitude arrays `A B : X → X → ℂ`, with environment a copy of `X`, such
that the rows of `A` and `B` have squared norms `p x` and `q x`, distinct
rows of `A` are orthogonal and distinct rows of `B` are orthogonal, and the
overlap satisfies `|∑ x, ∑ e, conj (A x e) * B x e| = ∑ x, √(p x * q x)`,
the Bhattacharyya coefficient of `p` and `q`.

The arrays are those of the vectors `∑ x, √(p x) |x⟩|x⟩` and `∑ x, √(q x)
|x⟩|x⟩`; orthogonality of the rows means that their reduced operators on the
system are exactly `diag p` and `diag q`. So the upper bound of the overlap
by the Bhattacharyya coefficient is attained.
