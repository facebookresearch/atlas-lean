---
article_id: af_1e78726a726b54509dfe9318
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.TheoryOfComputation.IntegerMultiplicationWanted.IntegerMultiplication.encodeNatBinary
---

# Encode Nat Binary

Binary encoding of a natural number: its base-2 digits, least
significant first. Its length is `Θ(log n)`, unlike Mathlib's unary
`Computability.encodeNat`; this is the size model of the cited
bit-complexity theorem, and using the unary encoding would make the
stated `O(n log n)` bound uninhabitable. This replaces the upstream unary encoding and is recorded as a Lean variant.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.TheoryOfComputation.IntegerMultiplicationWanted](../../../../sources/v2/WantedExt.md)
