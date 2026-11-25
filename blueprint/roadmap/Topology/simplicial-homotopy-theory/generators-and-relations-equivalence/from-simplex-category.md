# From Simplex Category

Explicit inverse-direction functor with canonical objects definitionally visible.
Object is definitionally `mk Δ.len`. Morphism uses fullness via `preimage` after
conjugating by the canonical equality at the boundary. Since the canonical
equality is `rfl`, `eqToHom` is definitionally `𝟙` and the conjugation is trivial;
we keep the `eqToHom` form to match the required interface. Functor laws follow
from faithfulness via `map_injective`.
