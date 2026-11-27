# Nakayama's lemma for finitely generated submodules

Let $R$ be a commutative ring with identity, let $I$ be an ideal of $R$ contained in the Jacobson radical of $R$, the intersection of all maximal ideals of $R$, and let $M$ be an $R$-module. If $N \subseteq M$ is a finitely generated submodule with $N \subseteq IN$, then $N = 0$. Since $IN \subseteq N$ always holds, the hypothesis says that $IN = N$. In particular, taking $N = M$: if $M$ is finitely generated and $IM = M$, then $M = 0$.

## Sources

- David Eisenbud, Commutative Algebra with a View Toward Algebraic Geometry, Graduate Texts in Mathematics 150, Springer-Verlag, 1995.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the Jacobson radical of a ring as the intersection of its maximal ideals: `Ring.jacobson_eq_sInf_isMaximal`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/Jacobson/Radical.lean#L129-L132.
