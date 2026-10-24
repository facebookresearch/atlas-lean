---
article_id: af_4dcde67b4df22c5cdda2cf02
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: IsDiscreteValuationRing.exists_generator_with_residue_minpoly_uniformizer
---

# Exists generator with residue minpoly uniformizer

Strengthening of `exists_adjoin_eq_top_of_separable_residueField`: the generator
`α` can be chosen together with a monic polynomial `F` over `A` lifting the residue
minimal polynomial, whose value at `α` is a uniformizer of `B`.
`F` is a monic lift of `minpoly (ResidueField A) (residue B α)`; it is in general
NOT `minpoly A α` — indeed `Polynomial.aeval α F` is a nonzero uniformizer, whereas
`aeval α (minpoly A α) = 0`. Separability makes the derivative value
`Polynomial.aeval α F.derivative` a unit. No claim is made about the different.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.RingTheory.DiscreteValuationRing.Monogenic](../../../../../sources/v2/MathlibExt.md)
