# Transport of ideal powers

Let `R,S` be commutative rings, `e : R ≃+* S` a ring equivalence, `I : Ideal R`, and `n : ℕ`.
Writing `J = I.map (e : R →+* S)`, this is an `e`-semilinear equivalence `I^n ≃ₛₗ[e] J^n`. It
sends `x` to `e x`, its inverse sends `y` to `e.symm y`, and scalar multiplication satisfies
`E (r • x) = e r • E x`.
