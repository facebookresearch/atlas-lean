# Finitely generated modules over a Noetherian ring are Noetherian

Let $R$ be a ring with identity, not necessarily commutative, that is left Noetherian: every left ideal of $R$ is finitely generated. Then every finitely generated left $R$-module $M$ is Noetherian: every submodule of $M$ is finitely generated. In particular, every finitely generated module over a Noetherian commutative ring with identity is a Noetherian module.

## Sources

- David Eisenbud, Commutative Algebra with a View Toward Algebraic Geometry, Graduate Texts in Mathematics 150, Springer-Verlag, 1995. For commutative rings.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for Noetherian rings as rings all of whose left ideals are finitely generated: `IsNoetherianRing`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/Noetherian/Defs.lean#L187-L191.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for Noetherian modules: `IsNoetherian`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/Noetherian/Defs.lean#L57-L62.
