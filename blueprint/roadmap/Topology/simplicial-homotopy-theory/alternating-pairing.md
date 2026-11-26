# Signed shuffles pair the two alternating-face complexes

Let C be a preadditive monoidal category with tensor product additive in both variables, and
let X and Y be simplicial objects. Assume the tensor complex of K_X and K_Y exists, where K
denotes the alternating-face complex. The shuffle map defines a chain pairing K_X ⊗ K_Y ⟶
K_(X⊗Y). In bidegree (p, q), its map X_p ⊗ Y_q ⟶ X_(p+q) ⊗ Y_(p+q) is ∑ s : Shuffle p q,
sign(s) • (X.map s.leftHom.op ⊗ₘ Y.map s.rightHom.op), with sign(s) the integer value of the
permutation sign.
