# Bar diagonal paired in a chosen bidegree

Let `G` be a group, `k` a commutative ring, `μ : M ⊗ N → P` a morphism of `k`-representations,
`n : ℕ`, and `s : Fin (n + 1)`. For bar cochains `φ : B_s → M` and `ψ : B_{n-s} → N`,
composing the degree-`n` bar diagonal with the `(s,n-s)` pairing descriptor equals the
following composite: transport `B_n` to the standard resolution, apply the linearized
simplicial diagonal and its front/back faces of degrees `s` and `n-s`, apply the transported
cochains `e.inv_s ≫ φ` and `e.inv_{n-s} ≫ ψ`, and then apply `μ`. Here `B` is the bar complex
and `e : B ≅ Rep.standardComplex k G`.
