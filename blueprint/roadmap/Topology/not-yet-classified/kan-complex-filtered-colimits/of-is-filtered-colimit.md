# Of Is Filtered Colimit

Filtered colimits of Kan complexes are Kan.

For a finite horn `Λ[n+1,i]` and a compatible family
`f : ∀ j ≠ i, Δ[n] ⟶ colim F`, the universal map
`φ = IsCompatible.desc hf : Λ[n+1,i] ⟶ colim F` factors through some
`F.obj j` because `Λ[n+1,i]` is finite hence finitely presentable
(`SSet.Finite → IsFinitelyPresentable`). The chosen representative
`φ' : Λ[n+1,i] ⟶ F.obj j` admits a Kan filler
`σ : Δ[n+1] ⟶ F.obj j` by `KanComplex.hornFilling`; then
`σ ≫ colimit.ι.app j` fills `f` in the colimit via `horn.ι_ι` and
`IsCompatible.ι_desc`.
