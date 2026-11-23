# Global Weil representation and theta functions

Let $F$ be a number field with adele ring $\mathbb{A}$, $\psi = \bigotimes_v \psi_v$ a non-trivial
character of $\mathbb{A}/F$, and $W$ a non-degenerate symplectic vector space over $F$ with a complete
polarization $W = X \oplus Y$ over $F$. The space of Schwartz–Bruhat functions on $X(\mathbb{A})$ is the
restricted tensor product $\mathcal{S}(X(\mathbb{A})) = \bigotimes'_v \mathcal{S}(X(F_v))$.

1. **Global metaplectic group.** The tensor product of the
   [local Weil representations](metaplectic-group-and-local-weil-representation.md)
   $\omega_{\psi_v}$ on the Schrödinger models $\mathcal{S}(X(F_v))$ is a projective representation of
   $\mathrm{Sp}(W)(\mathbb{A})$ on $\mathcal{S}(X(\mathbb{A}))$, which is an ordinary representation
   $\omega_\psi$ of a twofold cover $\mathrm{Mp}(W)(\mathbb{A})$ of $\mathrm{Sp}(W)(\mathbb{A})$.
2. **Weil's splitting.** The cover $\mathrm{Mp}(W)(\mathbb{A}) \to \mathrm{Sp}(W)(\mathbb{A})$ splits over
   the rational points $\mathrm{Sp}(W)(F)$, so $\mathrm{Sp}(W)(F)$ acts on $\mathcal{S}(X(\mathbb{A}))$.
3. **Theta distribution.** The distribution $\theta(\varphi) = \sum_{x \in X(F)} \varphi(x)$ on
   $\mathcal{S}(X(\mathbb{A}))$ is invariant under $\mathrm{Sp}(W)(F)$, and for each
   $\varphi \in \mathcal{S}(X(\mathbb{A}))$ the theta function
   $\theta_\varphi(g) = \theta(\omega_\psi(g)\varphi)$ is a continuous function on
   $\mathrm{Mp}(W)(\mathbb{A})$, left invariant under $\mathrm{Sp}(W)(F)$ and of moderate growth.
4. **Dual pairs.** If $(G_1, G_2)$ is a reductive dual pair in $\mathrm{Sp}(W)$ over $F$ and
   $\omega$ is a Weil representation of $G_1(\mathbb{A}) \times G_2(\mathbb{A})$ on
   $\mathcal{S}(X(\mathbb{A}))$ obtained from a splitting over $G_1(\mathbb{A}) \times G_2(\mathbb{A})$
   compatible with the rational points, such as the splittings of
   [unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), then
   $$\theta(\varphi)(g_1, g_2) = \sum_{x \in X(F)} \bigl(\omega(g_1, g_2)\varphi\bigr)(x)$$
   is a function on $G_1(F) \backslash G_1(\mathbb{A}) \times G_2(F) \backslash G_2(\mathbb{A})$, the
   automorphic realization of $\omega$.

Weil deduces the invariance in item 3 (his Théorème 6) from a generalized Poisson formula (his
Théorème 4 of Chapter I), which reduces to the Poisson summation formula over $X(F) \subset X(\mathbb{A})$
for the Weyl element exchanging $X$ and $Y$.

## Depends on

- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for the local Weil representations and their Schrödinger models
- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for automorphic forms and moderate growth on adelic groups

## Proof depends on

- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for the local splittings over the stabilizers of maximal isotropic subspaces and the local formulas of the Schrödinger models
- [Poisson summation formula for adeles](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/adelic-poisson-summation.md), for the invariance of the theta distribution under the Weyl element, which acts by a Fourier transform

## Sources

- D. Prasad, "A brief survey on the theta correspondence", in *Number Theory (Tiruchirapalli, 1996)*,
  Contemp. Math. 210, American Mathematical Society, 1998, 171–193; author's version
  <https://www.math.iitb.ac.in/~dprasad/dp.pdf>: §5, the paragraph before Theorem 7 (the global
  metaplectic cover), Theorem 7 (Weil's splitting) and the paragraph after it (the theta distribution,
  theta functions "slowly increasing and therefore automorphic", and theta lifts for dual pairs).
- A. Weil, "Sur certains groupes d'opérateurs unitaires", Acta Math. 111 (1964), 143–211,
  <https://doi.org/10.1007/BF02391012>: §41, Théorème 6 and formula (39), which Weil derives from
  Théorème 4 of Chapter I, n° 19, a formula that "se réduit à la formule de Poisson" for the Weyl
  element.
- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  §2.11 and §11.2 (the automorphic realization $\theta(\varphi)(g, h)$ for a dual pair).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states related results as `GlobalTheory.Published.WeilRepresentationExists` and
  `GlobalTheory.Published.ThetaRationalInvariance`.
