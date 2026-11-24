# Prism Tau eq non Degenerate Equiv val

Bridge to the upstream enumeration: `prismTau n k` is the
underlying simplex of `SSet.prodStdSimplex₁.nonDegenerateEquiv k`.
Hence the `nonDegenerateEquiv` API applies to `prismTau`
directly: values by
`SSet.prodStdSimplex₁.nonDegenerateEquiv_fst` and
`SSet.prodStdSimplex₁.nonDegenerateEquiv_snd`, faces by
`SSet.prodStdSimplex₁.δ_castSucc_nonDegenerateEquiv` and
`SSet.prodStdSimplex₁.δ_succ_nonDegenerateEquiv`, and ranges by
`SSet.prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₀_iff`
and `SSet.prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₁_iff`.
