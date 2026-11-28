# Initial form of a two-variable power series

For a commutative ring `W`, a natural number `d`, a power series `g` in two
variables over `W` and elements `p₀, p₁ ∈ W`, `initialForm d g p₀ p₁` is the
value at `(p₀, p₁)` of the degree-`d` homogeneous part of `g`: the finite
sum over `i ≤ d` of the coefficient of `X₀ ^ i X₁ ^ (d - i)` in `g` times
`p₀ ^ i p₁ ^ (d - i)`.
