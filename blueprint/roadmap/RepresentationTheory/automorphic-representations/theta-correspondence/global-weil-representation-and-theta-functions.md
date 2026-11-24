# Global Weil representation and theta functions

Let $F$ be a number field with adele ring $\mathbb{A}$, $\psi = \bigotimes_v \psi_v$ a non-trivial
character of $\mathbb{A}/F$, and $W$ a non-degenerate symplectic vector space over $F$ with a complete
polarization $W = X \oplus Y$ over $F$. The space of Schwartz–Bruhat functions on $X(\mathbb{A})$ is
$\mathcal{S}(X(\mathbb{A})) = \mathcal{S}(X(F_\infty)) \otimes \bigotimes'_{v < \infty} \mathcal{S}(X(F_v))$, with the full
Schwartz space of the real vector space $X(F_\infty) = \prod_{v \mid \infty} X(F_v)$ and the restricted tensor
product over the finite places with respect to the characteristic functions of $\mathcal{O}_v$-lattices
$X(\mathcal{O}_v)$ for a fixed $\mathcal{O}_F$-structure.

1. **Global metaplectic groups.** The tensor product of the
   [local Weil representations](metaplectic-group-and-local-weil-representation.md)
   $\omega_{\psi_v}$ on the Schrödinger models is a projective representation of
   $\mathrm{Sp}(W)(\mathbb{A})$ on $\mathcal{S}(X(\mathbb{A}))$. It is an ordinary representation $\omega_\psi$ of a
   central extension $\mathrm{Mp}(W)(\mathbb{A})$ of $\mathrm{Sp}(W)(\mathbb{A})$ by $\mathbb{C}^1$, and of a twofold
   cover $\mathrm{Mp}^{(2)}(W)(\mathbb{A}) \subset \mathrm{Mp}(W)(\mathbb{A})$, with
   $\mathrm{Mp}(W)(\mathbb{A}) = \mathrm{Mp}^{(2)}(W)(\mathbb{A}) \cdot \mathbb{C}^1$ the pushout of the twofold cover by
   $\mu_2 \subset \mathbb{C}^1$.
2. **Weil's splitting.** The twofold cover $\mathrm{Mp}^{(2)}(W)(\mathbb{A}) \to \mathrm{Sp}(W)(\mathbb{A})$ splits over
   the rational points $\mathrm{Sp}(W)(F)$, by a unique splitting, so $\mathrm{Sp}(W)(F)$ acts on
   $\mathcal{S}(X(\mathbb{A}))$.
3. **Theta distribution.** The distribution $\theta(\varphi) = \sum_{x \in X(F)} \varphi(x)$ on
   $\mathcal{S}(X(\mathbb{A}))$ is invariant under $\mathrm{Sp}(W)(F)$, and for each
   $\varphi \in \mathcal{S}(X(\mathbb{A}))$ the theta function
   $\theta_\varphi(g) = \theta(\omega_\psi(g)\varphi)$ is a continuous function on
   $\mathrm{Mp}^{(2)}(W)(\mathbb{A})$, left invariant under $\mathrm{Sp}(W)(F)$ and of moderate growth. No
   finiteness under a maximal compact subgroup is asserted for arbitrary $\varphi$.
4. **Dual pairs.** Let $(G_1, G_2)$ be a reductive dual pair in $\mathrm{Sp}(W)$ over $F$ and
   $\iota \colon G_1(\mathbb{A}) \times G_2(\mathbb{A}) \to \mathrm{Mp}(W)(\mathbb{A})$ a splitting into the $\mathbb{C}^1$-extension
   that agrees on rational points with the splitting of item 2, such as the splittings of
   [unitary dual pairs](weil-representation-of-unitary-dual-pairs.md) given by splitting characters.
   Such splittings need not lift to the twofold cover: at a real place where a factor $\mathrm{U}(1)$ acts as
   the rotation group $\mathrm{SO}(2) \subset \mathrm{SL}_2(\mathbb{R})$, the restriction of the twofold cover is the
   connected double cover of the circle, which has no continuous section. With
   $\omega = \omega_\psi \circ \iota$,

    $$\theta(\varphi)(g_1, g_2) = \sum_{x \in X(F)} \bigl(\omega(g_1, g_2)\varphi\bigr)(x)$$

    is a function on $G_1(F) \backslash G_1(\mathbb{A}) \times G_2(F) \backslash G_2(\mathbb{A})$, and
    $\varphi \mapsto \theta(\varphi)$ is the automorphic realization of $\omega$, a map into functions on this
    double quotient.

Weil deduces the invariance in item 3, in the $\mathbb{C}^1$-extension (his Théorème 6), from a generalized
Poisson formula (his Théorème 4 of Chapter I), which reduces to the Poisson summation formula over
$X(F) \subset X(\mathbb{A})$ for the Weyl element exchanging $X$ and $Y$; he proves separately (§45) that the
rational lift lies in the twofold cover, from the product formula for the local Weil indices of rational
quadratic forms (his §30, Proposition 5), from which Hilbert reciprocity follows and which Weil describes as
formally stronger than it.

## Depends on

- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for the local Weil representations and their Schrödinger models
- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for automorphic forms and moderate growth on adelic groups

## Proof depends on

- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for the local splittings over the stabilizers of maximal isotropic subspaces and the local formulas of the Schrödinger models
- [Poisson summation formula for adeles](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/adelic-poisson-summation.md), for the invariance of the theta distribution under the Weyl element, which acts by a Fourier transform: the formula, stated for the standard character $\psi_{\mathrm{std}}$ and scalar functions on $\mathbb{A}$, is applied coordinatewise to Schwartz functions on the vector space $X(\mathbb{A})$, on finite sums of products and then by continuity; for $\psi(x) = \psi_{\mathrm{std}}(ax)$ with $a \in F^\times$ the self-dual measure is unchanged since $\prod_v \lvert a \rvert_v = 1$, and the dual lattice $F$ is replaced by $a^{-1}F = F$
- [Additive duality of adeles and the volume of A/K](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/additive-duality-of-adeles.md), for the description of every non-trivial character of $\mathbb{A}/F$ as $x \mapsto \psi_{\mathrm{std}}(ax)$ with $a \in F^\times$
- [Product formula for principal ideles](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/adeles-and-ideles/adelic-norm-principal-embedding.md), for $\prod_v \lvert a \rvert_v = 1$, by which the self-dual measure does not change
- [Explicit formulas for the Weil representation](explicit-formulas-for-the-weil-representation.md), for the local Weil indices and the product formula for the Weil indices of rational quadratic forms (Weil, §30, Proposition 5), through which the rational lift lies in the twofold cover (item 2), and for the global compatibility of the splittings of unitary dual pairs used in item 4 for those pairs

## Sources

- D. Prasad, "A brief survey on the theta correspondence", in *Number Theory (Tiruchirapalli, 1996)*,
  Contemp. Math. 210, American Mathematical Society, 1998, 171–193; author's version
  <https://www.math.iitb.ac.in/~dprasad/dp.pdf>: §5, the paragraph before Theorem 7 (the global
  metaplectic cover), Theorem 7 (Weil's splitting) and the paragraph after it (the theta distribution,
  theta functions "slowly increasing and therefore automorphic", and theta lifts for dual pairs).
- A. Weil, "Sur certains groupes d'opérateurs unitaires", Acta Math. 111 (1964), 143–211,
  <https://doi.org/10.1007/BF02391012>: §41, Théorème 6 and formula (39), which Weil derives from
  Théorème 4 of Chapter I, n° 19, a formula that "se réduit à la formule de Poisson" for the Weyl
  element; §§42, 44–45 (the twofold covers, and the proof that the rational lift lies in the adelic
  twofold cover).
- C. Wu, "Irreducibility of theta lifting for unitary groups",
  arXiv:1409.0770 (preprint version): §2.1 (the metaplectic group as $\mathrm{Sp}(W) \times \mathbb{C}^1$) and §2.2 (splittings over
  dual pairs into this extension).
- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  §2.11 and §11.2 (the automorphic realization $\theta(\varphi)(g, h)$ for a dual pair).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states related results as `GlobalTheory.Published.WeilRepresentationExists` and
  `GlobalTheory.Published.ThetaRationalInvariance`.
