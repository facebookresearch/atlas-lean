# Exists preimage

Canonical-object fullness from the strong epi--mono factorization.

Uses `factorThruImage`, `image.ι`, and `image.fac` in `SimplexCategory`,
transports the image object to `mk (image θ).len` only at the outer boundary
via `SimplexCategory.ext` and `eqToHom`, then reuses `exists_preimage_of_epi`
and `exists_preimage_of_mono`.
