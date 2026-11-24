# Prod Map

Binary-product closure of `KanComplex.W`: from `W f` and `W g`, the product
map `Limits.prod.map f g` lies in `W`.

Hypotheses: `hf : W f` and `hg : W g`, universe-polymorphic in `u`.
Conclusion: `W (Limits.prod.map f g)` via `W.mk`. The Kan-source/target
components are proved here; the groupoid-equivalence component is provider
`SSet.isEquivalence_mapFundamentalGroupoid_prodMap` (former transitive seam
`ax_faithful_prodComparison`, now deleted in the provider) and the pointed-`π`
bijectivity component from the provider comparison. Uses no `ModelCategory SSet`
instance.
