---
article_id: af_b5b5bbf0223f64c31ac75a2b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Ideal.isPrime_map_of_coprime_clearDenom
---

# Is Prime map of coprime clear Denom

Primality of the extended ideal under denominator clearing.

If `algebraMap O B` is injective, `p` is prime, every `x ∈ c` clears denominators
uniformly, and `c ⊔ p = ⊤`, then `p.map (algebraMap O B)` is prime. The proof
builds the quotient isomorphism `O ⧸ p ≃+* B ⧸ p.map (algebraMap O B)` and
transports `IsDomain` across it.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.RingTheory.Ideal.PrimeExtension](../../../../../sources/v2/MathlibExt.md)
