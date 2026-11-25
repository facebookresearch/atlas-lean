# Poles of L-functions and nonvanishing of global theta lifts

This node is still to be broken down. It covers Yamana's criterion, combined with the tower property of global theta
lifting, as Gan, Qiu and Takeda use it in their proof of the Rallis inner product formula, here for unitary groups.
Let $E/F$ be a quadratic extension of number fields, $U_n$ a skew-Hermitian space of dimension $n \ge 1$ over $E$, and
$V_r = V_0 \oplus \mathbb{H}^r$ a Witt tower of Hermitian spaces over $E$, with $V_0$ anisotropic and $m = \dim V_r$; in the notation
of Gan, Qiu and Takeda, $\epsilon_0 = 0$, $d(n) = n$ and $s_{m,n} = (m - n)/2$. Fix a nontrivial character $\psi$ of $\mathbb{A}_F / F$ and
splitting characters, $\chi_V$ being a Hecke character of $\mathbb{A}_E^\times / E^\times$ with $\chi_V|_{\mathbb{A}_F^\times} = \varepsilon_{E/F}^m$, where $\varepsilon_{E/F}$ is the
quadratic character of $E/F$. Let $\pi$ be an irreducible cuspidal automorphic representation of $\mathrm{U}(U_n)$, $\Theta_{n,V}(\pi)$
its [global theta lift](global-theta-lifts.md) to $\mathrm{U}(V)$, and $\Theta_{n,j}(\pi)$ the lift to $\mathrm{U}(V_j)$.

- **The $L$-function.** $L(s, \pi \times \chi_V) = \prod_v L(s, \pi_v \times \chi_{V,v})$, the product over all places of $F$, where the local
  factor is that of the doubling zeta integrals
  $Z_v(s, \Phi_v, f_{1,v}, f_{2,v}) = \int_{\mathrm{U}(U_n)(F_v)} \Phi_v(g_v, 1) \, \overline{\langle \pi_v(g_v) f_{1,v}, f_{2,v} \rangle} \, dg_v$, formed with the
  conjugated matrix coefficient, as Gan, Qiu and Takeda write it after Lapid and Rallis and Yamana, whose gcd theorem
  identifies it at $s + \tfrac12$ with the gcd of the integrals for good sections. The conjugated coefficient is a coefficient of
  $\pi_v^\vee$, so in the convention of the ordinary coefficient $\langle \pi_v(g_v) f_{1,v}, f_{2,v} \rangle$ used by Lapid and Rallis and by
  Yamana this factor is $L_{\mathrm{LR}}(s, \pi_v^\vee \times \chi_{V,v})$, at every place, finite or archimedean, ramified or not. The two conventions differ: at a split place with $n = 1$, $\pi_v = \alpha$ and
  $\chi_{V,v} = (\beta, \beta^{-1})$ unramified with $\alpha(\varpi) = \beta(\varpi)$ a primitive sixth root of unity, the factor used here is $(1 - X)^{-2}$
  and $L_{\mathrm{LR}}(s, \pi_v \times \chi_{V,v})$ is $(1 + X + X^2)^{-1}$, with $X$ the Euler variable.
- **Theorem** (Gan, Qiu and Takeda's use of Yamana's Theorem 10.1 (2) with the tower property). Suppose that $n < m \le 2n$, $r \le n$ and $\Theta_{n,j}(\pi) = 0$ for $j < r$. If
  $L(s + \tfrac12, \pi \times \chi_V)$ is not holomorphic at $s = s_{m,n}$, then there is a Hermitian space $V^\#$ with
  $\chi_{V^\#} = \chi_{V_r}$ and $\dim V_r + \dim V^\# = 2n$ such that $\Theta_{n, V^\#}(\pi) \ne 0$.

This is the implication in Gan, Qiu and Takeda's proof of their Theorem 11.4 (ii), in their range, recorded at the level at which they use Yamana's theorem; Yamana's own statement is not restated here. The deduction from it
that $V^\#$ lies outside the tower of $V_r$, because the lower lifts vanish, belongs to the pages that use it.

## Expansion

A good expansion has a definition page for the twisted standard $L$-function through the doubling zeta integrals, in
the convention fixed above and independent of the page on the doubling method that uses this node, a statement page for Yamana's Theorem 10.1 (2) in
his own formulation, after reading S. Yamana, "L-functions and theta correspondence for classical groups", and a page
deducing the form above. That deduction uses the persistence of nonzero theta lifts up a Witt tower: if
$\theta_{n,r}(\varphi', f) \ne 0$, then for the mixed model of the Weil representation of $\mathrm{U}(V_{r+a})$ and a Schwartz function
$\varphi = \varphi' \otimes \varphi''$ with $\varphi''(0) = 1$, the constant term of $\theta_{n,r+a}(\varphi, f)$ along the stabilizer of an
isotropic subspace of dimension $a$ restricts to a nonzero multiple of $\theta_{n,r}(\varphi', f)$, so $\theta_{n,r+a}(\varphi, f) \ne 0$
(Wu, §3, Proposition 3.1). Gan, Qiu and Takeda state the implication for symplectic and unitary $G(U_n)$; the symplectic
case needs the corresponding constant term computation.

## Depends on

- [Global theta lifts of cusp forms](global-theta-lifts.md), for $\Theta_{n, V}(\pi)$

## Proof depends on

- [Constant terms of theta lifts for unitary groups](constant-terms-of-theta-lifts.md), for the constant term formula, which gives the persistence of nonzero global theta lifts up a Witt tower of Hermitian spaces

## Sources

- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and the Rallis inner
  product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3, TeX source): the proof of
  Theorem 11.4 (ii), TeX lines 4236–4242 ("By [Y4, Theorem 10.1 (2)] and the tower property of global theta lifting, if
  the $L$-function ... is not holomorphic at $s = s_{m,n}$, then there exists an $\epsilon$-Hermitian space $V^\#_{r'}$ with
  $\chi_{V^\#_{r'}} = \chi_{V_r}$ and $\dim V_r + \dim V^\#_{r'} = 2 \cdot d(n)$ such that the global theta lift ... is
  non-vanishing"), for $G(U_n)$ symplectic or unitary, and Theorem 11.4, TeX lines 4184–4228 (the range
  $d(n) < m \le 2 \cdot d(n)$, $r \le n$, $\pi$ irreducible cuspidal with $\Theta_{n,j}(\pi) = 0$ for $j < r$); TeX lines 742–752 ($V_r$, $m$,
  $\epsilon_0$ and $d(n)$), lines 3964–3968 ($\chi_V|_{\mathbb{A}^\times} = \chi_E^m$), lines 269 ff. and 4141–4155 (the doubling zeta integrals with the
  conjugated coefficient, the local factors of Lapid and Rallis and Yamana's gcd), and 4118–4180 (the twisted standard
  $L$-function), and §11.2 (the tower property, attributed to Rallis).
- S. Yamana, "L-functions and theta correspondence for classical groups", Invent. Math. 196 (2014), 651–732,
  Theorem 10.1 (2), as cited by Gan, Qiu and Takeda ([Y4]).
- C. Wu, "Irreducibility of theta lifting for unitary groups", arXiv:1409.0770 (preprint version): §3,
  Proposition 3.1, (3.2)–(3.4) (the constant terms of theta lifts, which give the tower property for unitary groups).
