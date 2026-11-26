# Weight-zero coefficient tensor as the coefficient carrier

For a commutative ring `k`, a `k`-algebra `A`, `P∈Over A`, and any coefficient module `M :
ModuleCat.{t} A`, there is an `A`-linear equivalence `M ⊗_A cotangentWeightZeroLevel k A P
≃ₗ[A] M`. It is the level isomorphism followed by `ULift.moduleEquiv`, removing the
categorical universe lift.
