---
article_id: af_ba8dcf3d1b1c46ee1a23f919
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Topology.ConwayKnotShared.KnotTheory.BraidClosure.applyCrossing
---

# Apply Crossing

Apply one braid generator to the traversal state. The crossing
occupies the `z`-slab `[zBot, zTop]` (with `zBot < zTop`). The braid
generator is `w = ±i`; we cross strands at positions `i` and `i + 1`,
with `i = w.natAbs`.

## Depends on

- [State](state.md)

## Proof depends on

- [Mk R3](mk-r3.md)
- [R3](../part-01/r3.md)

## Sources

- [WantedExt, WantedExt.Topology.ConwayKnotShared](../../../../../../sources/v2/WantedExt.md)
