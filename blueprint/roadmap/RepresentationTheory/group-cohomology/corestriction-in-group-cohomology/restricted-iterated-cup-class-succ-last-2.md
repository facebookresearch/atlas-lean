# One-factor mixed cup under the tensor-power identification

Let `G` be a group, `k` a commutative ring, `H ≤ G`, `A : Rep k G`, and `y ∈ H¹(H,Res A)`.
With no initial ambient factors, `restrictedIteratedCupClassSuccLast H A 0 (fun i => Fin.elim0
i) y = (Res((TensorPower.tensorPowObjOneIso A).inv))_* y`. Thus the result is `y` transported
to the coefficient `Res(A^{⊗1})`.
