---
article_id: af_5fb7d62f1ab962f61be39c93
declaration: structure
origin: cited
statement: formalized
lean: MathlibExt.Topology.ConwayKnotShared.KnotTheory.PLKnot
---

# PLKnot

A piecewise-linear closed polyline in `ℝ³` with at least three vertices.

Simplicity (being an embedded simple closed curve) is *not* bundled into the
structure; it is expressed separately as `PLKnot.IsSimple`. Keeping it out of
the structure lets named polylines such as `conwayKnot` be written down as
trusted, `sorry`-free data, with the finite-but-laborious simplicity proof
posed as its own benchmark obligation rather than carried as an unchecked
proof field.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Topology.ConwayKnotShared](../../../../../../sources/v2/WantedExt.md)
