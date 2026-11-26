# Tensor scalar extension along a ring homomorphism

For commutative rings `R : Type u`, `S : Type v`, and `f : R →+* S`, `extendScalars.{u,v,w} f`
sends a commutative `R`-algebra `P` to `S ⊗_{R,f} P`. Both source and target algebra carriers
have universe `max u v w`, and the `R`-action on `S` is induced by `f`.
