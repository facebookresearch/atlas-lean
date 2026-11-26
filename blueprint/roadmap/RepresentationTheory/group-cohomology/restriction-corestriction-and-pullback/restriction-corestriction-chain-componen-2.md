# Precomposition by the transfer component on arbitrary cochains

Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `T` a right transversal, `A
: Rep k G`, `n : ℕ`, and `f : (Fin n → G) → A`. For
`E_{T,n}=restrictionCorestrictionChainComponent T n`, `E_{T,n} ≫ Rep.freeLift k G A f =
Rep.freeLift k G A (corestrictionCochain A T n (fun q => f (fun i => (q i : G))))`. Hence
precomposition represents restriction followed by Schreier transfer on every degree-`n`
cochain.
