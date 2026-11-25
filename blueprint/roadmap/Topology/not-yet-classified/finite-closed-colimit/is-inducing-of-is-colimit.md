# Is Inducing of is Colimit

Inducing part of descent: `f` is inducing when `c` is colimiting,
`f` is globally injective, and each `f∘ι` is a closed embedding.
Proved by `TopologicalSpace.ext_isClosed` comparing `c.pt.str` with
`induced f`: the colimit side is `∀ j, IsClosed (ι⁻¹' S)` via
`nonempty_isColimit_iff_eq_coinduced` / `isClosed_sup_coinduced_iff`
(`isClosed_iff_of_isColimit`), the induced side is
`∃ T closed, S = f⁻¹' T` via `isClosed_induced_iff`; the bridge is
`S = f⁻¹' (f '' S)` (injectivity) and
`f '' S = ⋃ (f∘ι) '' (ι⁻¹' S)` (joint surjectivity + cover) which is
closed as a finite union of `IsClosedEmbedding.isClosedMap` images.
