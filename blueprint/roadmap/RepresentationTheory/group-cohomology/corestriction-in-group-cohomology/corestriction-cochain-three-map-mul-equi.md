# Three-cochain transfer under a group equivalence

Let `k` be a commutative ring, `e : G ≃* G'` a group equivalence, `H ≤ G` finite index, `T` a
right transversal, and `A : Rep k G'`. Put `H' = H.map e.toMonoidHom`, `q = H.mapMulEquivEquiv
e : H ≃* H'`, and `B = Rep.res e.toMonoidHom A`. For any cochain `f : H' × H' × H' → A`,
`(Tr_{e(T)}^A f)(e g₁,e g₂,e g₃) = Tr_T^B(f ∘ q³)(g₁,g₂,g₃)`, where `Tr` is the Schreier
three-cochain sum with weights `ρ(t⁻¹)`.
