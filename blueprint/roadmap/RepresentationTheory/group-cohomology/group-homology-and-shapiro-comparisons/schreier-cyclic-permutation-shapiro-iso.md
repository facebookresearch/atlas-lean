# Shapiro isomorphism for cyclic permutation coefficients

Let `G` be a group, `k` a commutative ring, `ℓ : ℕ` nonzero, `χ : G → Multiplicative (ZMod ℓ)`
a surjective group homomorphism, `A : Rep k G`, `T` a right transversal for `J=ker χ`, and `n
: ℕ`. Put `c(g)=Multiplicative.toAdd (χ g)`. The isomorphism `H^n(G,P_χ(A)) ≅ H^n(J,Res_J A)`
composes the coefficient comparison `p ↦ (g ↦ ρ_A(g)p(c(g)))` with Schreier Shapiro. Here
`P_χ(A)` has carrier `ZMod ℓ → A` and action `(g·p)(i)=ρ_A(g)p(i+c(g))`.
