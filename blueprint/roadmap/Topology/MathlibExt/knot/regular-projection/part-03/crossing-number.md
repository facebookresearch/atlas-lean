---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Topology.Knot.Euclidean.ParametrizedLink.crossingNumber
---

# Crossing Number

The crossing number of an oriented labeled ambient-isotopy type,
represented by `L`: the infimum, over all isotopic parametrized
representatives equipped with a regular standard projection, of the
number of double points of that projection. Changing the projection
direction is absorbed by varying the representative over its isotopy
class. The value is `⊤` in `ℕ∞` when no representative in the type is
known to admit a regular projection; existence of regular projections
in every type is the classical generic-direction theorem and is not
proved here.

## Depends on

- [Parametrized Link](../../euclidean-link/part-01/parametrized-link.md)

## Proof depends on

- [Is Regular Projection](../part-02/is-regular-projection.md)
- [Isotopic](../../euclidean-link/part-01/isotopic-2.md)
- [Crossing Count](../part-02/crossing-count.md)

## Sources

- [MathlibExt, MathlibExt.Topology.Knot.RegularProjection](../../../../../../sources/v2/MathlibExt.md)
