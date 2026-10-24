---
article_id: af_de3c50844402ff1a4773eacb
declaration: abbrev
origin: cited
statement: formalized
lean: MathlibExt.Topology.ConwayKnotShared.KnotTheory.disk2
---

# Disk2

The closed unit Euclidean `2`-disk `{(x, y) | x² + y² ≤ 1}`, the source
of a slicing disk's parametrization.

We spell the disk and its boundary out explicitly via `x² + y² ≤ 1` / `= 1`
rather than as `Metric.closedBall`/`Metric.sphere` on `ℝ × ℝ`: the product
norm on `ℝ × ℝ` is the *sup* norm, so `Metric.closedBall 0 1` would be the
*square* `[-1, 1]²` and `Metric.sphere 0 1` its cornered boundary. Smooth
slice-ness over a cornered domain is vacuously unsatisfiable — at a corner
no smooth immersion can match a corner-free smooth knot boundary while
keeping an injective derivative — which would make `Knot.SmoothlySlice`
false for *every* knot.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Topology.ConwayKnotShared](../../../../../../sources/v2/WantedExt.md)
