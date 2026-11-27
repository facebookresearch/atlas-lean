# Sphere Face Correction

Face correction along a rel-boundary homotopy, via Kan homotopy extension.

Assume `[KanComplex F]`. Given `H : HomotopyRel (stdSimplex.δ k ≫ w) v (boundary m)`,
a homotopy from the `k`-th face of `w` to `v`, stationary on `∂Δ[m]`, this produces
`w'` whose `k`-th face is exactly `v` (`δ k ≫ w' = v`) while every other face
`j ≠ k` is fixed (`δ j ≫ w' = δ j ≫ w`). See the module documentation.
