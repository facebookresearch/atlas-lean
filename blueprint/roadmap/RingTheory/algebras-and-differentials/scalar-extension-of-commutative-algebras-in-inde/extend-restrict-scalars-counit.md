# Counit of algebra scalar extension and restriction

Let `R : Type u`, `S : Type v` be commutative rings and `f : R →+* S`. The natural
transformation `restrictScalars f ⋙ extendScalars f → 𝟭 CommAlgCat S`, at carrier universe
`max u v w`, has component `S ⊗_R Res_f B → B` sending `s ⊗ b` to `s·b` for each commutative
`S`-algebra `B`.
