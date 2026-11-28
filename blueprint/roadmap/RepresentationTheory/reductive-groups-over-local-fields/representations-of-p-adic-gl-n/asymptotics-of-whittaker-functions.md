# Asymptotics of Whittaker functions of GLₙ over a non-archimedean field

This node is still to be broken down. It covers the asymptotic expansion of the Whittaker functions of a generic
representation of $\mathrm{GL}_n$ on the diagonal torus, uniform over the Whittaker model, from which the convergence and
rationality of the local Rankin–Selberg integrals follow. Let $F$ be a non-archimedean local field, $\psi$ a nontrivial
additive character, $\pi$ an irreducible generic representation of $\mathrm{GL}_n(F)$ with
[Whittaker model](whittaker-models-for-gl-n.md) $\mathcal{W}(\pi, \psi)$, $A$ the diagonal torus and
$\alpha_i(a) = a_i / a_{i+1}$ the simple roots. A function on $A$ is finite if its translates span a finite-dimensional space.

- **Theorem** (Matringe, Theorem 2.1; Cogdell, Proposition 6.1, for unitary $\pi$). There is a finite set $X(\pi)$ of finite
  functions on $A$, depending only on $\pi$, such that for every $W \in \mathcal{W}(\pi, \psi)$ there are
  [Schwartz–Bruhat functions](../representations-of-p-adic-reductive-groups/l-spaces-distributions-and-smooth-representations-of-l-groups.md) $\varphi_\chi$ on $F^{n-1}$, depending on $W$, with
  $W(a) = \sum_{\chi \in X(\pi)} \chi(a)\, \varphi_\chi(\alpha_1(a), \dots, \alpha_{n-1}(a))$ for $a = \mathrm{diag}(a_1, \dots, a_{n-1}, 1)$; the central
  character gives the dependence on the last coordinate.
- **Exponents** (Matringe, Theorem 2.1). The finite functions can be taken to be products of the characters by which the
  centres of the groups $\mathrm{GL}_k$ act on the irreducible subquotients of the nonzero
  [derivatives](bernstein-zelevinsky-derivatives.md) $\pi^{(n-k)}$, twisted by square roots of modulus characters and
  multiplied by powers of the valuation, with Schwartz functions that vanish at $0$ in the directions $k$ for which the
  derivative $\pi^{(n-k)}$ is zero.

## Expansion

A good expansion has a definition page for finite functions and statement pages for the expansion and for Matringe's
description of its exponents, each citing the sources below with locators. Matringe proves the description by induction
on $n$ through the derivatives, using the exactness of the Bernstein–Zelevinsky functors on representations of the
mirabolic subgroup.

## Depends on

- [Whittaker models and the Gelfand–Kazhdan theorems for GLₙ](whittaker-models-for-gl-n.md), for generic representations and their Whittaker models
- [Mirabolic restriction and Bernstein–Zelevinsky derivatives](bernstein-zelevinsky-derivatives.md), for the derivatives $\pi^{(n-k)}$
- [ℓ-spaces, distributions and smooth representations of ℓ-groups](../representations-of-p-adic-reductive-groups/l-spaces-distributions-and-smooth-representations-of-l-groups.md), for the Schwartz–Bruhat functions on $F^{n-1}$

## Proof depends on

- [Mirabolic restriction and Bernstein–Zelevinsky derivatives](bernstein-zelevinsky-derivatives.md), for the exactness of the functors on representations of the mirabolic subgroup and the restriction of Whittaker functions to it, in Matringe's induction
- [Parabolic induction and Jacquet functors](../representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md), for the Jacquet modules, whose central characters with Jordan blocks give finite functions of the form above

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in *Lectures on Automorphic
  L-functions*, Fields Institute Monographs 20, American Mathematical Society, 2004; author's version
  <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 6, pp. 45–46 (an irreducible admissible smooth unitary
  generic $\pi$), §1, Proposition 6.1 and Remarks 1–3, p. 46 (the expansion on the torus, uniform over $\mathcal{W}(\pi, \psi)$), with
  §2, Proposition 6.2, p. 47, as its application.
- N. Matringe, "Derivatives and asymptotics of Whittaker functions", arXiv:1004.1315 (version 2): §1, Case A (an arbitrary
  irreducible generic representation of $\mathrm{GL}_n$ over a non-archimedean local field), Proposition 2.1 (the exactness of the
  Bernstein–Zelevinsky functors), Propositions 2.2–2.8, and Theorem 2.1, p. 13, with its proof (the expansion with
  exponents given by the central characters of the derivatives).
