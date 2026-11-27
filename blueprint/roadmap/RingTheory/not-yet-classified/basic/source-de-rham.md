# Source De Rham

The de Rham complex of `B` over `A` in the form the descent of Tag 07HY consumes: the family
of `A`-linear differentials `d_{B/A} : Ω^p_{B/A} → Ω^{p+1}_{B/A}` on the exterior powers of the
Kähler differentials, subject to the defining rule on generators.  That rule pins the family down
uniquely (`KaehlerDifferential.deRhamDifferential_unique`), so the structure is a singleton:
`Stacks.DeRham.DifferentialDescent.sourceDeRham` is a term of it and
`Stacks.DeRham.DifferentialDescent.SourceDeRham.eq_sourceDeRham` says it is the only one.  The
complex property `d_{B/A} ∘ d_{B/A} = 0` is therefore nothing the structure asks for: its field
`complex` is filled in by default from `comp_eq_zero_of_gen`, which derives it from `gen`.
