# Linear-Hom and linear-Yoneda cochain complexes agree

Let `G` be a group, `k` a commutative ring, `A : Rep k G`, and `P` any `ℕ`-indexed chain
complex of representations. The canonical isomorphism identifies
`(linearHomCochainComplexFunctor k (Rep k G) A).obj (Opposite.op P)` with `P.linearYonedaObj k
A`. Their degree-`n` coefficient module is `Hom_{Rep k G}(P.X n,A)`, and the cochain
differential is precomposition by `P.d (n+1) n`.
