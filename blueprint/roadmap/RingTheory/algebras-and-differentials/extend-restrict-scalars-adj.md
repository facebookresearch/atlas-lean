# Tensor scalar extension is adjoint to algebra scalar restriction

Let `R : Type u` and `S : Type v` be commutative rings and `f : R →+* S`. On commutative
algebras of carrier universe `max u v w`, `extendScalars f ⊣ restrictScalars f`. The unit is
`a ↦ 1 ⊗ a`, and the counit is `s ⊗ b ↦ s·b`, giving `Hom_S(S ⊗_R A,B) ≅ Hom_R(A,Res_f B)`.
