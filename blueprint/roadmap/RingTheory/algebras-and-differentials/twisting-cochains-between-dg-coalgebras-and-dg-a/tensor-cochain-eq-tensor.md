# Tensor Cochain eq tensor

Diagonal specialization of the graded tensor product: on the same-source/target
`ModuleCat R` pair, `tensorCochain` agrees with the heterogeneous
`HomComplex.Cochain.tensor`. Both sides use the Koszul orientation
`(f ⊗ g)(x ⊗ y) = (-1) ^ (n * i₁) • (f x ⊗ g y)`. This bridge lets downstream
convolution reuse the heterogeneous functoriality/associativity API. It does not by
itself prove convolution associativity.
