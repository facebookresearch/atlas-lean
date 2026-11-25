# De Rham Differential smul ιMulti D

The defining rule of the de Rham differential:
`d (b₀ · d b₁ ∧ ⋯ ∧ d b_p) = d b₀ ∧ d b₁ ∧ ⋯ ∧ d b_p`.  The leading scalar `b₀` contributes the
factor `d b₀` through `dp_apply_smul`, and `G_exact` kills the wedge of exact forms.
