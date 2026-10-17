---
article_id: af_f4b9e8f87f00d1f89333aad5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ringKrullDim_le_of_integral
---

# Integral Krull Dim

Krull dimension cannot increase along an integral extension of commutative rings.

This is the dimension consequence of strict contraction of prime ideals
(`Ideal.IsIntegral.comap_lt_comap`): contraction gives a strictly monotone map
`PrimeSpectrum B → PrimeSpectrum A`, hence the inequality of Krull dimensions.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.RingTheory.Ideal.IntegralKrullDim](../../../../sources/v2/MathlibExt.md)
