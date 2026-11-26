# Adic evaluation of a power series

Let `R` and `S` be commutative rings, `S` an `R`-algebra, `J` an ideal of
`S`, `x : σ → S`, and `f` a multivariate power series over `R` in the
variables `σ`. `adicEval J x f` is the evaluation of `f` at `x`, obtained by
extending polynomial evaluation by continuity for the `J`-adic topology on
`S` and the discrete topology on `R`. On polynomials it is ordinary
polynomial evaluation; for general `f` it is meaningful when `S` is `J`-adically complete, each
coordinate `x_i` is topologically nilpotent, and the family `x` tends to `0`
along the cofinite filter on `σ` (automatic when `σ` is finite).
