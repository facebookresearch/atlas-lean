# Distinct variables form a regular sequence

Let `R` be a nontrivial commutative ring, `σ` a type, `n : ℕ`, and `f : Fin n → σ` injective.
The sequence `List.ofFn (fun i ↦ X_(f i))` is regular in `MvPolynomial σ R`. It is weakly
regular, and its generated ideal is proper because evaluation at zero maps its elements to
zero and maps `1` to the nonzero unit of `R`.
