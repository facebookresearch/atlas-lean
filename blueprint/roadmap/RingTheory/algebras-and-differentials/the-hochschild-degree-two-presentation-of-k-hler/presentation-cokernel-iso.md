# The categorical cokernel isomorphism

Let `k,A` be commutative rings with a `k`-algebra structure on `A`. Write `T₁ = A ⊗[k] A`, `T₂
= A ⊗[k] (A ⊗[k] A)`, `b₂(a ⊗ (b ⊗ c)) = ab ⊗ c - a ⊗ bc + ca ⊗ b`, and `η(a ⊗ b) = a • D k A
b : Ω¹(A/k)`. This is the isomorphism `cokernel b₂ ≅ ModuleCat.of A (Ω¹(A/k))` obtained from
the quotient equivalence `(T₁/im b₂) ≃ₗ[A] Ω¹(A/k)`. It sends the cokernel class of `a ⊗ b` to
`a db`.
