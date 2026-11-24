# Desc Of Truncation comp nerve Map

Universe-general postcomposition of truncated descent with a
functor, through `nerveMap`. Upstream `nerveMap` forces `D` and `E` to
share the universe pair `(u, v)`, but `u ≠ v` is allowed. The object
comparison is definitional (`nerveEquiv_nerveMap_app`), so the
`eqToHom` conjugations in `functor_ext` are handled by
`conj_eqToHom_iff_heq`.
