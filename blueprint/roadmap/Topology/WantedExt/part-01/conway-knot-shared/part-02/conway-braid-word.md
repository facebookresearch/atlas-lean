---
article_id: af_ca923fc300fbd49155e587f1
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Topology.ConwayKnotShared.KnotTheory.conwayBraidWord
---

# Conway Braid Word

A braid word for the Conway knot 11n34, on 4 strands, of length 11
and writhe `-1`. Each `±i` represents the braid generator `σ_i` (or its
inverse, for negative sign).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Topology.ConwayKnotShared](../../../../../../sources/v2/WantedExt.md)
- KnotInfo's `11n_34` record, `braid_notation` field. The Knot Atlas records a different but Markov-equivalent presentation for the same knot, `[1, 1, 2, -3, 2, 1, -3, -2, -2, -3, -3]` (which it labels `K11n34`, the mirror of the Conway knot); both representations agree on braid index 4, braid length 11, and writhe `-1`. Sliceness is mirror-invariant, so either braid word is a valid witness for `conway_knot_not_smoothly_slice`.
