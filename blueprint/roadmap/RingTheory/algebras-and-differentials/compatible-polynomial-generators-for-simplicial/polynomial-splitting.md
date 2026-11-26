# Polynomial coordinates on a simplicial splitting

Let `k : Type u` be a commutative ring and `P : SimplicialObject (CommAlgCat.{max u v} k)`. A
`PolynomialSplitting k P` contains a splitting `P.Splitting`, variable types `V_n`, and
isomorphisms `N_n ≅ MvPolynomial V_n k` for its nondegenerate summands. The splitting
expresses each `P_n` as a coproduct of the `N_m` indexed by simplex epimorphisms `[n] → [m]`.
