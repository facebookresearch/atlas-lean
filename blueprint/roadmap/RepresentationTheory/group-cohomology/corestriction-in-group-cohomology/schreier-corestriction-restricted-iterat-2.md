# Corestriction of right-associated iterated cups

Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, `n : ℕ`, `x :
Fin n → H¹(G,A)`, and `y ∈ H¹(H,Res A)`. For `P_n = TensorPower.tensorPowObjRightSucc A n`,
`schreierCorestriction H P_n (n + 1) (restrictedIteratedCupClassConsLast H A n x y) =
iteratedCupClassConsLast A n x (corestrictionH1 A y)` in `H^{n+1}(G,P_n)`.
