---
article_id: af_95e2acaa03ba1ee82ef5282f
declaration: structure
origin: cited
statement: formalized
lean: MathlibExt.Topology.AsphericalHomologySphereWanted.Topology.Closed4Manifold
---

# Closed4 Manifold

A closed connected topological 4-manifold, bundled with its topological-space
and chart instances so its existence can be quantified over. Charts model
`carrier` on `EuclideanSpace ℝ (Fin 4)` (the whole space, not a half-space), so
the space is locally Euclidean with no boundary; together with `CompactSpace`
this is a closed manifold. This is the charted topological-manifold model — it
carries `ChartedSpace`, not Mathlib's stronger bundled `IsManifold` class, which
is exactly right for a topological (not necessarily smooth) manifold.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Topology.AsphericalHomologySphereWanted](../../../../../sources/v2/WantedExt.md)
