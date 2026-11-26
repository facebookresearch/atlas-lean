# Unit of algebra scalar extension and restriction

Let `R : Type u`, `S : Type v` be commutative rings and `f : R →+* S`. The natural
transformation `extendScalarsUnit f : 𝟭 CommAlgCat R → extendScalars f ⋙ restrictScalars f`,
at carrier universe `max u v w`, has component `P → Res_f(S ⊗_R P)` sending `p` to `1 ⊗ p`.
