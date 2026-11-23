# Constant terms of theta lifts for unitary groups

This node is still to be broken down. It covers the computation, for unitary dual pairs, of the constant
terms of [global theta lifts](global-theta-lifts.md) along the parabolic subgroups of the target group,
which proves Rallis's tower property. Let $U$ be a skew-Hermitian space of dimension $n$ and
$V_r = V_0 \oplus \mathbb{H}^r$ a Witt tower of Hermitian spaces over a quadratic extension $E/F$ of number
fields, with the Weil representations fixed by the same $\psi$, $\chi_U$ and $\chi_V$ along the tower, and $\pi$ a
cuspidal automorphic representation of $\mathrm{U}(U)(\mathbb{A})$.

- **Mixed model.** For the stabilizer $Q_a$ in $\mathrm{U}(V_r)$ of an isotropic subspace $X_a$ of dimension
  $a \le r$, the realization of the Weil representation on $\mathcal{S}(X_a^n \oplus \dots)$ adapted to
  $V_r = X_a \oplus V_{r-a} \oplus X_a^*$ and the action of $Q_a$ in it.
- **Constant term formula.** For $f \in \pi$ and $\varphi$ in the mixed model, the constant term of
  $\theta_{n,r}(\varphi, f)$ along $Q_a$, restricted to the Levi factor $\mathrm{GL}(X_a) \times \mathrm{U}(V_{r-a})$, equals the
  theta lift $\theta_{n,r-a}(\varphi(\cdot, 0), f)$ to $\mathrm{U}(V_{r-a})$, multiplied by a character of
  $\mathrm{GL}(X_a)$ given by $\chi_U \circ \det$ and a power of $\lvert \det \rvert$: in the unfolding, the terms of non-zero rank
  vanish by cuspidality of $f$ and the zero orbit gives the smaller lift; absolute convergence justifies the
  exchange of integrals.

A good expansion has pages for the mixed model and for the constant term formula with its character and
modulus, each with a precise statement and the sources below.

## Depends on

- [Global theta lifts of cusp forms](global-theta-lifts.md), for the theta lifts along a Witt tower

## Sources

- C. Wu, "Irreducibility of theta lifting for unitary groups",
  arXiv:1409.0770 (preprint version): §2.5 (the mixed model) and §3, Proposition 3.1, (3.2)–(3.4) (the constant term formula),
  with its proof (3.22)–(3.25) and the exchange of integrals; p. 2 (Rallis's symplectic–orthogonal
  computation does not readily apply to general unitary groups).
- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  §11.2 (the tower property, attributed to Rallis).
