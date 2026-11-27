# Ideal criterion for flatness of a module over a commutative ring

Let $R$ be a commutative ring with identity and let $M$ be an $R$-module. Then $M$ is flat over $R$ if and only if, for every ideal $I$ of $R$, the map $I \otimes_R M \to R \otimes_R M$ obtained by tensoring the inclusion $I \hookrightarrow R$ with the identity of $M$ is injective.

Here *flat* has its usual meaning: for every injective homomorphism $f\colon N \to P$ of $R$-modules, the map $f \otimes 1_M\colon N \otimes_R M \to P \otimes_R M$ is injective. Mathlib defines flatness by the special case in which $P$ is a finitely generated $R$-module (in the same universe as $R$) and $f$ is the inclusion of a finitely generated submodule $N$, and proves that this special case implies the usual condition.

## Sources

- David Eisenbud, Commutative Algebra with a View Toward Algebraic Geometry, Graduate Texts in Mathematics 150, Springer-Verlag, 1995.
- The Stacks Project Authors, *The Stacks Project*, Lemma 10.39.5, Tag 00HD, https://stacks.math.columbia.edu/tag/00HD.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the definition of flatness: `Module.Flat`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Flat/Basic.lean#L108-L116.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the usual condition implied by it: `Module.Flat.rTensor_preserves_injective_linearMap`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Flat/Basic.lean#L120-L122.
