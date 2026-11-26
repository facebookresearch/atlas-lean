# Inhomogeneous cochain on a bar basis vector

Let `A` be a `k`-representation of a group `G`, with `k` commutative. For `n : ℕ`, an
inhomogeneous cochain `φ : (Fin n → G) → A`, a tuple `f : Fin n → G`, `g : G`, and `r : k`,
its equivariant bar cochain evaluates `single f (MonoidAlgebra.single g r)` to `r • A.ρ g (φ
f)`.
