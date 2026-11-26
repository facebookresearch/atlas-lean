# Coefficient lift to the joint tensor carrier universe

Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. The functor
`cotangentWeightZeroCoefficientLift k A : ModuleCat.{t} A → ModuleCat.{max u v t} A` sends `M`
to `ULift.{max u v} M`, with the transported `A`-action, and sends a coefficient map to its
lifted linear map.
