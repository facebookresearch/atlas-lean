# Affine Horn Retract

Piecewise-affine retraction onto the horn locus.

Subtract the minimum off every non-`k` coordinate and add `n * minimum`
to `k`. The construction uses `Finsupp.equivFunOnFinite` directly, without
any bridge.
