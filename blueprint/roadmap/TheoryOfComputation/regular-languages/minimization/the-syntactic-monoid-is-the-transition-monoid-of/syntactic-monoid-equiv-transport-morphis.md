# Syntactic Monoid Equiv Transport morphism

The transported equivalence sends the syntactic class of a word to the same
transition monoid element as the original equivalence. Stated in simp-normal form,
at the coercion `(x : SyntacticMonoid L₂)`, since `simp` rewrites
`syntacticMorphism L₂ x` to that coercion (`syntacticMorphism_apply`).
