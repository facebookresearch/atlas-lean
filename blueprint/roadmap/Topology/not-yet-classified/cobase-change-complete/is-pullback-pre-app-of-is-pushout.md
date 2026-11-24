# Precomposition turns pushouts into pullbacks

For a pushout
square `IsPushout i f f' j` of simplicial sets and any simplicial set
`C`, the induced square of functor objects

```text
Fun(Y, C) ⟶ Fun(B, C)
   |            |
   v            v
Fun(X, C) ⟶ Fun(A, C)
```

is a pullback square in `SSet`. The lift of a cone `s` is the curry
of the map out of the pushout tensored with `s.pt` classifying the
two uncurried cone legs, which agree over `A ⊗ s.pt` by
`MonoidalClosed.uncurry_pre_app` and the cone condition; the
factorization and uniqueness clauses are the dual computation with
`MonoidalClosed.curry_pre_app`, `MonoidalClosed.uncurry_curry` and
`IsPushout.inl_desc`/`IsPushout.inr_desc`/`IsPushout.hom_ext`. This
discharges TODO(T26-C)(1) of the `CobaseChange.lean` header.
