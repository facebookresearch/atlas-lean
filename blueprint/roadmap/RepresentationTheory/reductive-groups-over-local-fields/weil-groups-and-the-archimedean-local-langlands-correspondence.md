# Weil groups of local fields and the archimedean local Langlands correspondence for GLₙ

This node is still to be broken down. It covers the Weil groups and Langlands parameters that the pages on the
local Langlands correspondence, on base change and on archimedean $L$-factors use.

- **Weil groups of $p$-adic fields.** Let $F$ be a finite extension of $\mathbb{Q}_p$, with algebraic closure $\bar F$ and
  residue field of order $q$. The Weil group $W_F$ is the subgroup of $\mathrm{Gal}(\bar F/F)$ of the elements acting on
  the residue field of $\bar F$ by an integral power of Frobenius. It is topologized so that the inertia subgroup $I_F$
  is open with its profinite topology; this is not the topology induced from $\mathrm{Gal}(\bar F/F)$, but the inclusion
  is continuous with dense image. Its abelianization $W_F^{\mathrm{ab}}$ is the quotient by the closure of the commutator
  subgroup, its maximal abelian Hausdorff quotient. The reciprocity map $\mathrm{Art}_F \colon F^\times \to W_F^{\mathrm{ab}}$ is an
  isomorphism of topological groups, mapping $\mathcal{O}_F^\times$ onto the image of $I_F$ and uniformizers to geometric
  Frobenius elements. Followed by the injection of $W_F^{\mathrm{ab}}$ into $\mathrm{Gal}(\bar F/F)^{\mathrm{ab}}$, it is
  $x \mapsto \theta_F(x)^{-1}$, where $\theta_F$ is the local Artin map normalized by arithmetic Frobenius. For a finite
  extension $E/F$, $W_E$ is an open subgroup of finite index of $W_F$, so representations of $W_E$ induce to $W_F$.
  Representations of $W_F$ are continuous and finite dimensional. An unramified representation is one trivial on
  inertia; an unramified semisimple representation of dimension $n$ is determined by the conjugacy class of the image
  of a geometric Frobenius element.
- **Unramified parameters.** Every irreducible representation $\pi$ of $\mathrm{GL}_n(F)$ with a nonzero
  $\mathrm{GL}_n(\mathcal{O}_F)$-fixed vector is the unramified constituent of the representation normalized-induced from
  unramified characters $\chi_1, \dots, \chi_n$ of $F^\times$ (Casselman), and is determined by the $S_n$-orbit of
  $(\chi_1(\varpi), \dots, \chi_n(\varpi))$, its Satake parameter. Its Langlands parameter is the unramified representation
  $\bigoplus_i \chi_i \circ \mathrm{Art}_F^{-1}$ of $W_F$, on which a geometric Frobenius element acts with eigenvalues
  $\chi_1(\varpi), \dots, \chi_n(\varpi)$. This identification of the Satake parameter with the Frobenius class is a
  normalization of the correspondence; it does not follow from the determination of unramified representations by
  Frobenius.
- **Archimedean Weil groups.** $W_{\mathbb{C}} = \mathbb{C}^\times$, and $W_{\mathbb{R}} = \mathbb{C}^\times \cup j\mathbb{C}^\times$ with
  $jzj^{-1} = \bar z$ and $j^2 = -1$, an extension of $\mathrm{Gal}(\mathbb{C}/\mathbb{R})$ by $\mathbb{C}^\times$, topologized so
  that $\mathbb{C}^\times$, with its usual topology, is an open subgroup of index $2$. The isomorphism
  $W_{\mathbb{R}}^{\mathrm{ab}} \cong \mathbb{R}^\times$ sends $z$ to $z \bar z$ and $j$ to $-1$. The normalized absolute values are
  $\lvert x \rvert_{\mathbb{R}} = \lvert x \rvert$ and $\lvert z \rvert_{\mathbb{C}} = z \bar z$. Representations of $W_k$ are continuous, finite
  dimensional and semisimple; discontinuous characters of $\mathbb{C}^\times$ are excluded. The irreducible ones have
  dimension $1$ or $2$: the characters of $k^\times$ through $W_k^{\mathrm{ab}}$, and, for $k = \mathbb{R}$, the
  representations $\tau_{\ell, t}$ for integers $\ell \ge 1$ and $t \in \mathbb{C}$, with a basis $u, u'$ such that
  $re^{i\theta}$ acts by $r^{2t} e^{i\ell\theta}$ on $u$ and by $r^{2t} e^{-i\ell\theta}$ on $u'$, $ju = u'$ and $ju' = (-1)^\ell u$.
- **Archimedean local Langlands correspondence for $\mathrm{GL}_n$** (Langlands). For $k = \mathbb{R}$ or $\mathbb{C}$ there is a
  bijection $\tau \mapsto \pi(\tau)$ from the $n$-dimensional representations of $W_k$ onto the irreducible admissible
  smooth representations of moderate growth of $\mathrm{GL}_n(k)$ (equivalently, by Casselman and Wallach, the
  irreducible admissible $(\mathfrak{g}, K)$-modules). Characters of $W_k^{\mathrm{ab}} = k^\times$ correspond to characters of
  $\mathrm{GL}_1(k)$, and $\tau_{\ell, t}$ to the discrete series $D_\ell \otimes \lvert \det \rvert^t$ of $\mathrm{GL}_2(\mathbb{R})$. For
  $\tau = \bigoplus_{i=1}^r \tau_i$ with $\tau_i$ irreducible of dimension $n_i$ and exponent $t_i$, ordered so that
  $\operatorname{Re} t_1 / n_1 \ge \dots \ge \operatorname{Re} t_r / n_r$, the representation normalized-induced from
  $\pi(\tau_1) \otimes \dots \otimes \pi(\tau_r)$ on the block upper triangular parabolic subgroup is a standard module, and
  $\pi(\tau)$ is its unique irreducible quotient, the Langlands quotient.
- **Factors.** With $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$ and $\Gamma_{\mathbb{C}}(s) = 2(2\pi)^{-s}\Gamma(s)$, Weil attached
  $L(s, \tau)$ and $\varepsilon(s, \tau, \psi)$ to representations of $W_k$, multiplicatively on direct sums:
  $L(s, \tau \oplus \tau') = L(s, \tau) L(s, \tau')$ and likewise for $\varepsilon$. For instance
  $L(s, \lvert \cdot \rvert_k^r) = \Gamma_k(s + r)$ with the normalized absolute value, and
  $L(s, \tau_{\ell, t}) = \Gamma_{\mathbb{C}}(s + t + \ell/2)$. For representations $\pi$ of $\mathrm{GL}_n(k)$ and $\pi'$ of
  $\mathrm{GL}_m(k)$, $L(s, \pi \times \pi') = L(s, \tau(\pi) \otimes \tau(\pi'))$ and
  $\varepsilon(s, \pi \times \pi', \psi) = \varepsilon(s, \tau(\pi) \otimes \tau(\pi'), \psi)$, where $\tau(\pi)$ is the parameter of $\pi$.

## Expansion

A good expansion has definition pages for the Weil groups of $p$-adic and archimedean local fields and for unramified
parameters, and statement pages for the unramified correspondence, for the archimedean local Langlands correspondence
for $\mathrm{GL}_n$ and for Weil's archimedean $L$- and $\varepsilon$-factors, each citing the sources below with locators.
Langlands's classification of real groups is by $L$-packets; that the packets of $\mathrm{GL}_n(k)$ are single
representations, so that the correspondence is a bijection, is part of Knapp's account.

## Depends on

- [Local class field theory: the local Artin map](../../NumberTheory/p-adic-numbers/local-class-field-theory.md), for the local Artin map $\theta_F$ of a finite
  extension of $\mathbb{Q}_p$, normalized by arithmetic Frobenius; the reciprocity map $\mathrm{Art}_F$ is its composite with
  inversion, with values in the dense subgroup $W_F^{\mathrm{ab}}$
- [Admissible representations of real reductive groups](representations-of-real-reductive-groups/admissible-representations-of-real-reductive-groups.md), for the representations of
  $\mathrm{GL}_n(\mathbb{R})$ and $\mathrm{GL}_n(\mathbb{C})$
- [Casselman–Wallach globalization theorem](representations-of-real-reductive-groups/casselman-wallach-globalization.md), for the equivalence between representations of moderate growth and $(\mathfrak{g}, K)$-modules
- [Discrete series representations and formal degrees](representations-of-real-reductive-groups/discrete-series-and-formal-degrees.md), for the discrete series of $\mathrm{GL}_2(\mathbb{R})$ attached to the two-dimensional parameters

## Proof depends on

- [Characters, principal series and the Langlands classification for real reductive groups](representations-of-real-reductive-groups/principal-series-of-real-reductive-groups.md), for the Langlands classification by standard modules and their Langlands quotients, which the correspondence specializes to $\mathrm{GL}_n(k)$

## Sources

- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2), for $p$-adic fields: (1.1.6)–(1.1.10) (the Weil group as the inverse image of the
  integral powers of Frobenius, its topology, the alternative definition through Weil classes, the maximal abelian
  Hausdorff quotient, and $\mathrm{Art}_K \colon K^\times \cong W_K^{\mathrm{ab}}$ sending uniformizers to geometric Frobenius
  elements), (3.1.5) (restriction and induction along $W_L \subset W_K$), and (4.1.1)–(4.1.8) (unramified representations,
  Casselman's theorem, the Satake parameter and the unramified correspondence, normalized through $\mathrm{Art}_K$).
- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 8, §1, pp. 61–62 (the Weil groups $W_{\mathbb{C}}$ and $W_{\mathbb{R}}$ and the arithmetic Langlands
  classification for $\mathrm{GL}_n(k)$, with Casselman–Wallach), and §2, pp. 62–63 (Weil's $L$- and $\varepsilon$-factors,
  $\Gamma_k$, and the factors of pairs through the classification).
- A. W. Knapp, "Local Langlands correspondence: the archimedean case", in *Motives*, Proc. Sympos. Pure Math. 55,
  Part 2, American Mathematical Society, 1994, 393–410: Theorems 2 and 5, pp. 403 and 406 (the bijections for
  $\mathrm{GL}_n(\mathbb{R})$ and $\mathrm{GL}_n(\mathbb{C})$, through the Langlands quotients of standard modules ordered by the
  real parts of the normalized exponents, with the parameters $\tau_{\ell, t}$ and the discrete series $D_\ell$).
- R. P. Langlands, "On the classification of irreducible representations of real algebraic groups", in
  *Representation theory and harmonic analysis on semisimple Lie groups*, Math. Surveys Monogr. 31, American
  Mathematical Society, 1989, 101–170, the classification by $L$-packets of Langlands parameters, as cited by Cogdell.
