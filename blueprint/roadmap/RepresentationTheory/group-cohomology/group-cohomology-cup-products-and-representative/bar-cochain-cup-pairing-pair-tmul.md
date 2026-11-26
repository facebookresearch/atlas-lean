# Cup product of two bar cochains

Let `G` be a group, `k` a commutative ring, and `A,B` representations. For `p,q : ℕ` and
equivariant bar cochains `φ : (Rep.barComplex k G).X p → A`, `ψ : (Rep.barComplex k G).X q →
B`, the graded cup pairing sends `φ ⊗ₜ[k] ψ` to `barComplexDiagonal G k` in degree `p + q`
followed by `linearYonedaPairingDesc (𝟙 (A ⊗ B)) p q φ ψ`.
