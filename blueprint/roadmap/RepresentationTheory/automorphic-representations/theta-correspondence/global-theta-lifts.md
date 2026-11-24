# Global theta lifts of cusp forms

Let $F$ be a number field, $E/F$ a quadratic extension, $U$ a skew-Hermitian space of dimension $n \ge 1$
over $E$, and $V_0$ an anisotropic Hermitian space of dimension $m_0$; for $j \ge 0$ let
$V_j = V_0 \oplus \mathbb{H}^j$, with $\mathbb{H}$ the hyperbolic plane, be the Witt tower of $V_0$, so
that $V_r$ has dimension $m = m_0 + 2r$ and Witt index $r$. Fix $\psi$ and Hecke characters
$(\chi_U, \chi_V)$ as in [the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md),
the same for the whole tower (the condition on $\chi_V|_{\mathbb{A}_F^\times}$ depends only on $m$ modulo $2$), let
$\omega$ be the Weil representation of $\mathrm{U}(U)(\mathbb{A}) \times \mathrm{U}(V_r)(\mathbb{A})$ on
$\mathcal{S}(X_r)(\mathbb{A})$ for an $F$-rational polarization $\mathrm{Res}_{E/F}(U \otimes_E V_r) = X_r \oplus Y_r$, and
$\theta(\varphi)(g, h)$ its automorphic realization. When $V_j = 0$ (a split tower, $m_0 = 0$, $j = 0$), the Schwartz space
is $\mathbb{C}$ and $\mathrm{U}(U)(\mathbb{A})$ acts on it by the character $\chi_V \circ \iota^{-1} \circ \det$, where $\iota(x) = x / x^c$
identifies $\mathbb{A}_E^\times / \mathbb{A}_F^\times$ with the norm-one ideles (this character need not be trivial). Let $\pi$ be a
cuspidal automorphic representation of
$\mathrm{U}(U)(\mathbb{A})$, realized on a space of
[cusp forms](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md).

1. **Theta lifts.** For every Schwartz function $\varphi \in \mathcal{S}(X_r)(\mathbb{A})$ and every $f \in \pi$ the
   integral

    $$\theta_{n,r}(\varphi, f)(h) = \int_{\mathrm{U}(U)(F) \backslash \mathrm{U}(U)(\mathbb{A})} \theta(\varphi)(g, h)\, \overline{f(g)}\, dg,$$

    for the Tamagawa measure $dg$, converges absolutely and defines a smooth function of moderate growth on
    $\mathrm{U}(V_r)(F) \backslash \mathrm{U}(V_r)(\mathbb{A})$ (for $V_r = 0$, the number $\varphi \int \chi_V(\iota^{-1}(\det g))\, \overline{f(g)}\, dg$). If
    $\varphi$ is finite under the maximal compact subgroup $K_\infty$ of $\mathrm{U}(V_r)(F_\infty)$ used to define automorphic
    forms, then $\theta_{n,r}(\varphi, f)$ is $K_\infty$-finite and, by the correspondence of infinitesimal characters,
    finite under the centre of the enveloping algebra, hence an automorphic form. The global theta lift $\Theta_{n,r}(\pi)$ is the space spanned
    by the $\theta_{n,r}(\varphi, f)$, a representation of $\mathrm{U}(V_r)(\mathbb{A})$ in the space of smooth automorphic
    functions of Gan–Qiu–Takeda (without the condition of finiteness under a maximal compact subgroup); it may
    be zero, and no irreducibility is asserted.

2. **Tower property** (Rallis). If $\Theta_{n,j}(\pi) = 0$ for every $j < r$, then every function in
   $\Theta_{n,r}(\pi)$ is cuspidal: its constant terms along all proper parabolic subgroups of $\mathrm{U}(V_r)$ vanish.
   For $r = 0$ there is nothing to prove, since $\mathrm{U}(V_0)$ has no proper parabolic subgroup over $F$.

## Depends on

- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for $\omega$ and its automorphic realization
- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cusp forms, cuspidal automorphic representations and automorphic forms on unitary groups

## Proof depends on

- [Rapid decay of cusp forms](../automorphic-forms-on-reductive-groups/rapid-decay-of-cusp-forms.md), for the rapid decrease of $f$ on Siegel sets, against which the moderate growth of $\theta(\varphi)$ is integrated
- [Global Weil representation and theta functions](global-weil-representation-and-theta-functions.md), for the moderate growth of theta functions
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the covering of $\mathrm{U}(U)(F) \backslash \mathrm{U}(U)(\mathbb{A})$ by a Siegel set of finite volume
- [Constant terms of theta lifts for unitary groups](constant-terms-of-theta-lifts.md), for the computation of the constant term of $\theta_{n,r}(\varphi, f)$ along the stabilizer of an isotropic subspace of $V_r$ as a theta lift to a smaller space of the tower (down to $V_0$, possibly $0$), which gives item 2
- [Classical invariant theory and harmonics](classical-invariant-theory-and-harmonics.md), for the correspondence of infinitesimal characters, through which the lift of a $K_\infty$-finite datum is finite under the centre of the enveloping algebra (Gan, §§1.2 and 3.6)

## Sources

- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  §1.1 (the global theta lift, with the Tamagawa measure), §2.9, (2.2) (the one-dimensional model for
  $V_0 = 0$, with the character $\chi \circ \iota^{-1} \circ \det$), §2.10 (smooth automorphic forms, without the
  usual $K$-finiteness condition), §2.2 (Witt towers), §11.1 (the unitary dual
  pairs, $\epsilon_0 = 0$) and §11.2 (the definition of $\Theta_{n,r}(\pi)$ and "a well-known result of
  Rallis [R1] says that $\Theta_{n,r}(\pi)$ is contained in the space of cusp forms" when
  $\Theta_{n,j}(\pi) = 0$ for $j < r$).
- D. Prasad, "A brief survey on the theta correspondence", in *Number Theory (Tiruchirapalli, 1996)*,
  Contemp. Math. 210, American Mathematical Society, 1998, 171–193; author's version
  <https://www.math.iitb.ac.in/~dprasad/dp.pdf>: §5, the paragraph after Theorem 7 ("$\theta_\varphi(f)$
  is an automorphic form on $G_2$, and is called the theta lift of $f$"), and §6, Theorem 9 (Rallis's
  towers, for symplectic–orthogonal pairs).
- S. Rallis, "Injectivity properties of liftings associated to Weil representations", Compositio Math. 52
  (1984), 139–169, <http://www.numdam.org/item?id=CM_1984__52_2_139_0>: introduction and item (VIII) of the preliminaries
  (the tower decomposition of the cuspidal spectrum, from S. Rallis, Compositio Math. 51 (1984),
  Theorem 1.2.1, for symplectic–orthogonal pairs).
- W. T. Gan, "Automorphic forms and the theta correspondence", lecture notes, arXiv:2303.14918 (version
  1): §1.2, p. 2 (smooth automorphic functions, finite under the centre of the enveloping algebra) and §3.6,
  p. 26 (the global theta lift lands in that space).
- C. Wu, "Irreducibility of theta lifting for unitary groups",
  arXiv:1409.0770 (preprint version): §2.5 and §3, Proposition 3.1, (3.2)–(3.4) (the constant terms of theta lifts for
  unitary groups; Wu notes that Rallis's symplectic–orthogonal computation does not apply directly).
