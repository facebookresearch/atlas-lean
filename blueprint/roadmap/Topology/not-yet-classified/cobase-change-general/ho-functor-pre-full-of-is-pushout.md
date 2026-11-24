# Fullness of precomposition with a cobase change (TODO(T31-B)(1), unconditional)

**Fullness of precomposition with a cobase change
(TODO(T31-B)(1), unconditional).** In a pushout square
`IsPushout i f f' j` with `i` a monomorphism and `f` a categorical
equivalence, precomposition with `f'` induces a full functor on
homotopy categories of functor objects into every quasicategory
`C`. The proof is §3 of the module header: represent the given
morphism by an edge of `Fun(B, C)`, take a preimage edge in
`Fun(X, C)` through the equivalence `hFun(f, C)`, correct the first
edge by `SSet.exists_edge_correction_of_innerFibration` (packet
T31, inner horn `Λ[2, 1]` through the inner fibration
`(pre i).app C`) so the two edges agree strictly in `Fun(A, C)`,
and glue along `SSet.isPullback_pre_app_of_isPushout` (packet
T30).
