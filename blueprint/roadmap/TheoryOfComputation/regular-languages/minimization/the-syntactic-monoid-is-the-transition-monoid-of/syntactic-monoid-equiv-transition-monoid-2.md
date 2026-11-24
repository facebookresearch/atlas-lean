# Syntactic Monoid Equiv Transition Monoid To DFA morphism

The canonical isomorphism for `L.toDFA` sends the syntactic class of a word to the
transition monoid element of that word. Stated in simp-normal form: `simp` rewrites
`syntacticMorphism L x` to the coercion `(x : SyntacticMonoid L)`
(`syntacticMorphism_apply`), so the lemma is stated at the coercion.
