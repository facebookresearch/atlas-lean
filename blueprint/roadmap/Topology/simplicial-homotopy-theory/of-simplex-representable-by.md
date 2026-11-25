# Standard simplex compatibility backport for Lean 4.33

If a simplex `x : X _⦋n⦌` is such that `yonedaEquiv.symm x : Δ[n] ⟶ X` is a
monomorphism, then `Subcomplex.ofSimplex x` is representable by `⦋n⦌`.
