# Head-tail formula for mixed iterated cups

Let `G` be a group, `k` a commutative ring, `H ≤ G`, `A : Rep k G`, `n : ℕ`, `x : Fin (n + 1)
→ H¹(G,A)`, and `y ∈ H¹(H,Res A)`. Applying `(Rep.resTensorPowHeadTailIso H.subtype A n).hom`
in degree `n + 2` to the mixed tensor-power cup equals `cupOneAny (Res A) (Res(A^{⊗(n+1)})) (n
+ 1) (res(x 0) ⊗ restrictedIteratedCupClassSuccLast H A n (fun i => x i.succ) y)`.
