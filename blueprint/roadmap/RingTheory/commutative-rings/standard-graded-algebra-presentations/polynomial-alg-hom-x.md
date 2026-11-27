# A polynomial variable evaluates to its specified generator

Let A and S be commutative rings, S an A-algebra, and Sgrade : ℕ → Submodule A S an internal
graded-algebra decomposition. Let hstd be a standard presentation with r degree-one
generators. For every i : Fin r, hstd.polynomialAlgHom (MvPolynomial.X i) = (hstd.generator i
: S).
