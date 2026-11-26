# Polynomial comonad on the slice over an algebra

For a commutative ring `k` and `k`-algebra `A`, `polynomialOverComonad k A` is the polynomial
comonad lifted to `Over A`. On `P=(B→A)`, its underlying object is `T(B)` and its structure
map to `A` is the polynomial counit `T(B)→B` followed by `P.hom`.
