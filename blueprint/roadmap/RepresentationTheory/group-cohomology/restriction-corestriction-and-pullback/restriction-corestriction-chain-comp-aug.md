# Transfer chain map lifts multiplication by the index

Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
Write `P=Rep.barResolution k G`, `ε=P.π`, and `E_T=restrictionCorestrictionChain T`. Then `E_T
≫ ε = ε ≫ (ChainComplex.single₀ (Rep k G)).map (H.index • 𝟙 (Rep.trivial k G k))`. Thus `E_T`
lifts index multiplication on the trivial representation resolved by `P`.
