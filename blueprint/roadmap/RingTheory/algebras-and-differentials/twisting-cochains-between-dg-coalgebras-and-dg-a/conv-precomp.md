# Conv precomp

Convolution commutes with precomposition by a comonoid morphism.

For `f : Cochain C A m`, `g : Cochain C A n`, and `ψ : C' ⟶ C` with
`IsComonHom ψ`, precomposing `conv f g` equals the convolution of the
precomposed factors. The proof reuses the heterogeneous tensor precomposition
coherence and the cochain lift of `IsComonHom.hom_comul`.
