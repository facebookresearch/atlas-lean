# Is Closed T1 Embedding of is Pushout

Pushout stability for closed T1-embeddings.

Reuses the accepted closed-embedding pushout theorem
`TopCat.isClosedEmbedding_of_isPushout` for the `IsClosedEmbedding`
half. For the relative-T1 condition, let `y ∈ X₄` with `y ∉ Set.range b`.
Then `b ⁻¹' {y} = ∅` and `(t ≫ r) ⁻¹' {y} = ∅` (since
`Set.range (t ≫ r) ⊆ Set.range b`), both closed. The remaining
preimage `r ⁻¹' {y}` is the fiber over `y` in `X₂`. Any `x ∈ r ⁻¹' {y}`
satisfies `x ∉ Set.range t` (otherwise `y = r (t s) = b (l s) ∈
Set.range b`), and `r` is injective on `X₂ \ Set.range t` – the
generating relation for the `Type` pushout only identifies
`inl (t s)` with `inr (l s)` – so `r ⁻¹' {y}` is at most a
singleton outside `Set.range t`. Hence it is either `∅` or `{x}` with
`x ∉ Set.range t`, closed by `ht`'s T1 condition. The three preimages
being closed gives `IsClosed {y}` in the colimit via
`TopCat.isClosed_iff_of_isColimit`. The complement-injectivity of `r`
is proved via the Sierpinski test space and the pushout universal
property.
