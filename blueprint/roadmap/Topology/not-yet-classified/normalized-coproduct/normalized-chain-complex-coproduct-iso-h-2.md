# Normalized Chain Complex Coproduct Iso hom naturality of mono

For a monomorphism `f : X ⟶ Y` of simplicial sets, the normalized chain map
in degree `n`, transported via the canonical coproduct isomorphisms
`normalizedChainComplexCoproductIso`, coincides with coproduct reindexing along
the embedding `nonDegenerateEmbeddingOfMono f n` of nondegenerate simplices.

In other words, the square
```
∐_{X.nonDeg n} R  --iso_X-->  (X.normalizedChainComplex R).X n
      |                                |
sigmaConst.map embedding          (normalizedChainComplexMap f R).f n
      v                                v
∐_{Y.nonDeg n} R  --iso_Y-->  (Y.normalizedChainComplex R).X n
```
commutes, i.e. source coproduct to source normalized chains to target
normalized chains equals source coproduct reindexed into the target coproduct
and then mapped by the target canonical isomorphism.
