# Composite algebra action for scalar restriction

Let `R : Type u` and `S : Type v` be commutative rings, `f : R →+* S`, and `A : CommAlgCat.{w}
S`. The structure `restrictedAlgebra f A : Algebra R A` has structural map `R → A` equal to
`algebraMap S A ∘ f`, as defined by `Algebra.compHom A f`.
