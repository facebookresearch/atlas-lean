# Regular tensor unitor with the coefficient universe lift

Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, and `M : ModuleCat.{t}
A`. The isomorphism `M ⊗_A A ≅ ULift.{max u v} M` in the joint carrier category is the regular
tensor unitor followed by the coefficient lift. It sends `m ⊗ a` to `ULift.up (a • m)`.
