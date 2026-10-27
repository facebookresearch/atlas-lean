---
article_id: af_5ad0aeaf05edf97682b6a15f
declaration: def
origin: cited
statement: formalized
lean: Metric.IsDeltaHyperbolic
---

# Is Delta Hyperbolic

A pseudometric space `X` is `δ`-hyperbolic (in the sense of Gromov) if `0 ≤ δ` and the
Gromov product satisfies the four-point inequality
`(x ∣ z)_w ≥ min (x ∣ y)_w (y ∣ z)_w - δ` for all points `w x y z`, where
`(x ∣ y)_w = Metric.gromovProduct x y w` (basepoint third, as in Mathlib).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Topology.MetricSpace.GromovHyperbolic](../../../../../sources/v2/MathlibExt.md)
