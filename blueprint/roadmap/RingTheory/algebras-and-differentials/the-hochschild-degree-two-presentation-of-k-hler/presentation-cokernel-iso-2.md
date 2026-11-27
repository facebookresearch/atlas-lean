# The cokernel map is the differential map

Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Write `T₁ = A ⊗[k] A`, `T₂
= A ⊗[k] (A ⊗[k] A)`, `b₂(a ⊗ (b ⊗ c)) = ab ⊗ c - a ⊗ bc + ca ⊗ b`, and `η(a ⊗ b) = a • D k A
b : Ω¹(A/k)`. Let `π : T₁ → cokernel b₂` be the cokernel projection and `E : cokernel b₂ ≅
Ω¹(A/k)` the presentation isomorphism. Then `E.hom ∘ π = η`, or categorically `cokernel.π
(presentation k A).f ≫ (presentationCokernelIso k A).hom = (presentation k A).g`.
