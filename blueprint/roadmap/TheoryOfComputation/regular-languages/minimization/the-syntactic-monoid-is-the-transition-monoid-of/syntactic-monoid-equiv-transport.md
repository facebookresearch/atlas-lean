# Syntactic Monoid Equiv Transport

Transport a syntactic-monoid equivalence along a language equality. Given
`e : SyntacticMonoid L₁ ≃* TransitionMonoid M` and `h : L₁ = L₂`, this is the
`SyntacticMonoid L₂ ≃* TransitionMonoid M` obtained by rewriting `h` in `e`; on
`syntacticMorphism` terms it sends the syntactic class of a word to the same
transition monoid element. The three canonical specializations below are instances
of this helper at the `accepts` equalities.
