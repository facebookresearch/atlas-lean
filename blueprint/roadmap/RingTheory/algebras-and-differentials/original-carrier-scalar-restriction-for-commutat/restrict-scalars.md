# Scalar restriction functor for commutative algebras

For commutative rings `R : Type u`, `S : Type v`, and `f : R →+* S`, `restrictScalars f :
CommAlgCat.{w} S → CommAlgCat.{w} R` retains each algebra's carrier and ring operations and
uses the composite `R→S→A` action. Each morphism retains its underlying ring map. The carrier
universe `w` is independent of `u,v`.
