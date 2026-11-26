# Pullback naturality of arbitrary cochain cup degrees

Let `k` be a commutative ring, `f : G →* H` a group homomorphism, `A,B : Rep k H`, and `A',B'
: Rep k G`. For `φ : Rep.res f A → A'`, `ψ : Rep.res f B → B'`, put `θ = (Rep.resTensorIso f A
B).inv ≫ (φ ⊗ ψ)` and `c_n(f,φ) = (cochainsMap f φ).f n`. For `p,q : ℕ`, the cup pairings
satisfy `P_H(A,B).pair p q ≫ c_{p+q}(f,θ) = (c_p(f,φ) ⊗ c_q(f,ψ)) ≫ P_G(A',B').pair p q`.
