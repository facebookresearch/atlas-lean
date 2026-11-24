# Core

The *core* of a simplicial set `X`: the subcomplex of simplices
whose every edge is an equivalence. Precisely, a simplex
`x : X.obj Δ` belongs to `core X` when for every map
`φ : ⦋1⦌ ⟶ Δ.unop`, the edge `Edge.mk' (X.map φ.op x)` cut out by
`φ` is an `Edge.IsEquivalence`.

Quantifying over all `φ` (not only injective ones) is the formulation
the `SSet.Edge` API supports best: stability under `X.map f` is then
formal, the non-injective maps contribute only degenerate identity
edges (`isEquivalence_mk'_map_const`), and
`mem_core_obj_iff_forall_edge` recovers the injective vertex-pair
formulation.
