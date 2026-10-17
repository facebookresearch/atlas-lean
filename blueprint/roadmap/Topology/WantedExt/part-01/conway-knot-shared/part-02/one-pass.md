---
article_id: af_d2c3d8024b6d27c66e94f57b
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Topology.ConwayKnotShared.KnotTheory.BraidClosure.onePass
---

# One Pass

One pass through the braid box plus a closure arc. If the pass ends
at position `1`, the closure arc closes back to the polyline's starting
vertex `(1, 0, 0)` and we omit the redundant final vertex. Otherwise
we continue at the top of the new position.

## Depends on

- [State](state.md)

## Proof depends on

- [Apply Word](apply-word.md)
- [Mk R3](mk-r3.md)
- [R3](../part-01/r3.md)

## Sources

- [WantedExt, WantedExt.Topology.ConwayKnotShared](../../../../../../sources/v2/WantedExt.md)
