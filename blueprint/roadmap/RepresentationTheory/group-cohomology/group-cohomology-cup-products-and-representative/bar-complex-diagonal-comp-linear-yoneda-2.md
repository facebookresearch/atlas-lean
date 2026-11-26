# Bar diagonal paired in total degree

Let `G` be a group, `k` a commutative ring, and `μ : M ⊗ N → P` a morphism of representations.
For `p,q : ℕ` and bar cochains `φ : B_p → M`, `ψ : B_q → N`, the composite `Δ_B,p+q ≫
linearYonedaPairingDesc μ p q φ ψ` is the standard-resolution front/back Alexander–Whitney
split followed by `(e.inv_p ≫ φ) ⊗ (e.inv_q ≫ ψ)` and `μ`. The input is first transported by
`e.hom_{p+q}`, where `e : B ≅ Rep.standardComplex k G`.
