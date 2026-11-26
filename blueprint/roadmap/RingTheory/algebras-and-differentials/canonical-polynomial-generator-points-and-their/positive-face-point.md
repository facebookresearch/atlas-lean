# Positive faces preserve polynomial generator points

Let `k` be a commutative ring, `A` a `k`-algebra, `n : ℕ`, `i : Fin(n+1)`, and `x∈T^{n+1}A`.
The face `δ_{i+1}:P_{n+1}→P_n` sends `point_{n+1}(x)` to `point_n(ε_i(x))`, where
`ε_i=Comonad.cobarEpsilonAtPos (polynomialComonad k) n i A : T^{n+1}A→T^n A` applies the
counit at the indicated position.
