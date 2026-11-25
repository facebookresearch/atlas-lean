# SHORTEST VECTOR PROBLEM IN THE MAX NORM is NP-complete

The SHORTEST VECTOR PROBLEM IN THE MAX NORM decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a basis `(v₁, …, v_k)` for a lattice in `ℤᵏ`, and a positive integer `K`. Question: does the lattice contain a vector `v = x₁v₁ + ⋯ + x_kv_k` with integers `(x₁, …, x_k) ≠ (0, …, 0)` and all coordinates of `v` bounded by `K` in absolute value, that is, `‖v‖_∞ ≤ K`?

## Sources

- P. van Emde Boas, "Another NP-complete partition problem and the complexity of computing short vectors in a lattice", Report 81-04, Mathematisch Instituut, University of Amsterdam (1981), p. 2, problem CLOSEST VECTOR and Theorem 2.
- D. Micciancio, "The shortest vector in a lattice is hard to approximate to within some constant", SIAM J. Comput. 30 (2001), 2008-2035, doi:10.1137/S0097539700373039, Section 1 and footnote 1 (van Emde Boas's "Closest Vector" is the shortest vector problem in the `ℓ∞` norm).
