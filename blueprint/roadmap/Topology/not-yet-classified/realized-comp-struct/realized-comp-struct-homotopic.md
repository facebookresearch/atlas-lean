# Realized Comp Struct Homotopic

Realized composition structure as path homotopy (universe-polymorphic).

From `h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂` in `SSet.{u}`, the realized direct edge is
`Path.Homotopic` to the concatenation of realized `e₀₁` then `e₁₂`, with orientation and
endpoints exactly matching `realizedEdgePath` and `Path.trans`. Both sides are
`_root_.Path (realizedVertex x₀) (realizedVertex x₂)`.
