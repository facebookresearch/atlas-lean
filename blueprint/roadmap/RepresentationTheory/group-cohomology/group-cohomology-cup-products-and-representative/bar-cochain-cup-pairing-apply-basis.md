# Bar cup product evaluated on an inhomogeneous tuple

Let `A,B` be representations of a group `G` over a commutative ring `k`, and let `φ,ψ` be
equivariant bar cochains of degrees `p,q : ℕ`. Transport their bar cup product to
inhomogeneous cochains and evaluate it at `g : Fin (p + q) → G`. The result is `(Δ_{p+q} ≫
linearYonedaPairingDesc (𝟙 (A ⊗ B)) p q φ ψ)` evaluated at `Finsupp.single g
(MonoidAlgebra.single 1 1)`, where `Δ` is the bar chain diagonal.
