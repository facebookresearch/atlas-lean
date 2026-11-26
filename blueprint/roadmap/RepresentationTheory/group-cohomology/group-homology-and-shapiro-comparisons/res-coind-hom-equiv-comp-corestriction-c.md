# Adjoint composition through the finite-index counit

Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `X,A : Rep k G`, and `Y :
Rep k H`. Given `r : Res X → Y` and `z : Y → Res A`, write `α=Rep.resCoindHomEquiv H.subtype X
(Res A)`, `β=(Rep.resIndAdjunction k H).homEquiv X Y`, and `γ=(Rep.indResHomEquiv H.subtype Y
A).symm`. Then `α(r ≫ z) ≫ corestrictionCounit H A = β(r) ≫ γ(z)` as morphisms `X → A`; the
right-hand composite factors through `Ind_H^G Y`.
