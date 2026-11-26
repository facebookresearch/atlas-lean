# Composition of scalar restriction functors

Let `R : Type u`, `S : Type v`, and `T : Type z` be commutative rings, with `f : R→+*S`, `g :
S→+*T`. On `T`-algebras of carrier universe `w`, `restrictScalars (g.comp f) ≅ restrictScalars
g ⋙ restrictScalars f`. The components preserve the algebra elements and identify the two
composite scalar actions.
