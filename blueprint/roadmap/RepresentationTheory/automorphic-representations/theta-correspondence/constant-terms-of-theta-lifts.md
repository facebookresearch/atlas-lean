# Constant terms of theta lifts for unitary groups

This node is still to be broken down. It covers the computation, for unitary dual pairs, of the constant
terms of the theta lifts $\theta_{n,r}(\varphi, f)(h) = \int \theta(\varphi)(g, h)\, \overline{f(g)}\, dg$ of cusp forms $f$ along the
parabolic subgroups of the target group, which proves Rallis's tower property for
[global theta lifts](global-theta-lifts.md). Let $U$ be a skew-Hermitian space of dimension $n \ge 1$ and
$V_r = V_0 \oplus \mathbb{H}^r$ a Witt tower of Hermitian spaces over a quadratic extension $E/F$ of number
fields, with the Weil representations fixed by the same $\psi$, $\chi_U$ and $\chi_V$ along the tower, and $\pi$ a
cuspidal automorphic representation of $\mathrm{U}(U)(\mathbb{A})$. When $V_0 = 0$ the bottom of the tower carries the
one-dimensional model, on which $\mathrm{U}(U)(\mathbb{A})$ acts by $\chi_V \circ \iota^{-1} \circ \det$ with $\iota(x) = x/x^c$.

- **Mixed model.** For the stabilizer $Q_a$ in $\mathrm{U}(V_r)$ of an isotropic subspace $X_a$ of dimension
  $1 \le a \le r$, the realization of the Weil representation on
  $\mathcal{S}((U \otimes X_a)(\mathbb{A})) \otimes \mathcal{S}(X_{r-a}')(\mathbb{A})$ adapted to $V_r = X_a \oplus V_{r-a} \oplus X_a^*$, where
  $X_{r-a}'$ is a rational Lagrangian of $\mathrm{Res}_{E/F}(U \otimes V_{r-a})$ (the second factor being $\mathbb{C}$ with the
  one-dimensional model when $V_{r-a} = 0$), and the action of $Q_a$ in it.
- **Constant term formula.** For $f \in \pi$ and $\varphi$ in the mixed model, the constant term of
  $\theta_{n,r}(\varphi, f)$ along $Q_a$, restricted to the Levi factor $\mathrm{GL}(X_a) \times \mathrm{U}(V_{r-a})$, equals the
  theta lift $\theta_{n,r-a}(\varphi(0, \cdot), f)$ to $\mathrm{U}(V_{r-a})$, on which $b \in \mathrm{GL}(X_a)(\mathbb{A}_E)$ acts by
  $\chi_U(\det b)\, \lvert \det b \rvert_{\mathbb{A}_E}^{n/2}$ (for the unnormalized constant term, in Wu's coordinates): in the
  unfolding, the terms of non-zero rank vanish by cuspidality of $f$ and the zero orbit gives the smaller
  lift. The exchange of the integrations over $\mathrm{U}(U)(F) \backslash \mathrm{U}(U)(\mathbb{A})$ and over the compact quotient of the
  unipotent radical of $Q_a$ is justified by absolute convergence, which follows from the rapid decay of $f$, the
  moderate growth of the theta kernel and the finite volume of a Siegel set, uniformly on the compact quotient.

A good expansion has pages for the mixed model and for the constant term formula with its character and
modulus, each with a precise statement and the sources below.

## Depends on

- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for the Weil representations of the unitary dual pairs of positive dimension along a Witt tower and their theta functions
- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cusp forms, cuspidal automorphic representations and constant terms

## Proof depends on

- [Rapid decay of cusp forms](../automorphic-forms-on-reductive-groups/rapid-decay-of-cusp-forms.md), for the rapid decrease of $f$ on Siegel sets
- [Global Weil representation and theta functions](global-weil-representation-and-theta-functions.md), for the moderate growth of the theta kernel
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the covering by a Siegel set of finite volume, which with the two previous inputs gives the absolute convergence used to exchange the integrations

## Sources

- C. Wu, "Irreducibility of theta lifting for unitary groups",
  arXiv:1409.0770 (preprint version): §2.5 (the mixed model) and §3, Proposition 3.1, (3.2)–(3.4) (the constant term formula,
  with the character $\chi_1 \circ \det \cdot \lvert \det \rvert_{\mathbb{A}_E}^{\dim Y/2}$), with its proof, p. 12 (absolute integrability and the
  exchange of integrals); p. 2 (Rallis's symplectic–orthogonal computation does not readily apply to general
  unitary groups).
- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  §2.9, (2.2) (the one-dimensional model at the bottom of a split tower) and §11.2 (the tower property,
  attributed to Rallis).
