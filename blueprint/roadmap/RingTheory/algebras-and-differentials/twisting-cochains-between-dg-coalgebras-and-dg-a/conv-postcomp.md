# Conv postcomp

Convolution commutes with postcomposition by a monoid morphism.

For `f : Cochain C A m`, `g : Cochain C A n`, and `φ : A ⟶ B` with
`IsMonHom φ`, postcomposing `conv f g` equals the convolution of the
postcomposed factors. The proof reuses the heterogeneous tensor postcomposition
coherence and the cochain lift of `IsMonHom.mul_hom`.
