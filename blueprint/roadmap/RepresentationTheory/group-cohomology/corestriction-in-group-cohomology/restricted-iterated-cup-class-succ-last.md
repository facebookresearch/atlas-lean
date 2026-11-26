# Mixed iterated cup in an ambient tensor power

Let `G` be a group, `k` a commutative ring, `H ≤ G`, `A : Rep k G`, and `n : ℕ`. For `x : Fin
n → H¹(G,A)` and `y ∈ H¹(H,Res A)`, `restrictedIteratedCupClassSuccLast H A n x y` is the
iterated cup of the restricted `x`-classes followed by `y`, with degree `n + 1` and
coefficient `Rep.res H.subtype (TensorPower.tensorPowObj A (n + 1))`.
