# Global theta lifts of cusp forms

Let $F$ be a number field, $E/F$ a quadratic extension, $U$ a skew-Hermitian space of dimension $n$ over
$E$, and $V_0$ an anisotropic Hermitian space of dimension $m_0$; for $j \ge 0$ let
$V_j = V_0 \oplus \mathbb{H}^j$, with $\mathbb{H}$ the hyperbolic plane, be the Witt tower of $V_0$, so
that $V_r$ has dimension $m = m_0 + 2r$ and Witt index $r$. Fix $\psi$ and Hecke characters
$(\chi_U, \chi_V)$ as in [the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md)
(the restriction of $\chi_V$ to $\mathbb{A}_F^\times$ depends only on $m$ modulo $2$), let $\omega$ be the
Weil representation of $\mathrm{U}(U)(\mathbb{A}) \times \mathrm{U}(V_r)(\mathbb{A})$ on
$\mathcal{S}(X)(\mathbb{A})$ and $\theta(\varphi)(g, h)$ its automorphic realization. Let $\pi$ be a
cuspidal automorphic representation of $\mathrm{U}(U)(\mathbb{A})$, realized on a space of
[cusp forms](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md).

1. **Theta lifts.** For $\varphi \in \mathcal{S}(X)(\mathbb{A})$ and $f \in \pi$ the integral
   $$\theta_{n,r}(\varphi, f)(h) = \int_{\mathrm{U}(U)(F) \backslash \mathrm{U}(U)(\mathbb{A})} \theta(\varphi)(g, h)\, \overline{f(g)}\, dg,$$
   for the Tamagawa measure $dg$, converges absolutely and defines an automorphic form on
   $\mathrm{U}(V_r)(\mathbb{A})$. The global theta lift $\Theta_{n,r}(\pi)$ is the automorphic
   representation of $\mathrm{U}(V_r)(\mathbb{A})$ spanned by these functions.
2. **Tower property** (Rallis). If $\Theta_{n,j}(\pi) = 0$ for every $j < r$, then $\Theta_{n,r}(\pi)$ is
   contained in the space of cusp forms on $\mathrm{U}(V_r)(\mathbb{A})$.

## Depends on

- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for $\omega$ and its automorphic realization
- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cusp forms, cuspidal automorphic representations and automorphic forms on unitary groups

## Proof depends on

- [Rapid decay of cusp forms](../automorphic-forms-on-reductive-groups/rapid-decay-of-cusp-forms.md), for the rapid decrease of $f$ on Siegel sets, against which the moderate growth of $\theta(\varphi)$ is integrated
- [Global Weil representation and theta functions](global-weil-representation-and-theta-functions.md), for the moderate growth of theta functions
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the covering of $\mathrm{U}(U)(F) \backslash \mathrm{U}(U)(\mathbb{A})$ by a Siegel set of finite volume
- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for the formulas of the Weil representation along the parabolic subgroups of $\mathrm{U}(V_r)$ through which the constant terms of $\theta_{n,r}(\varphi, f)$ are expressed by theta lifts to $\mathrm{U}(V_j)$, $j < r$

## Sources

- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  §1.1 (the global theta lift, with the Tamagawa measure), §2.2 (Witt towers), §11.1 (the unitary dual
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
