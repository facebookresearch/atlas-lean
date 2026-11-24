# Weil groups of local fields and the archimedean local Langlands correspondence for GLₙ

This node is still to be broken down. It covers the Weil groups and Langlands parameters that the pages on the
local Langlands correspondence, on base change and on archimedean $L$-factors use.

- **Weil groups.** For a non-archimedean local field $F$ with algebraic closure $\bar F$ and residue field of order
  $q$, the Weil group $W_F$ is the subgroup of $\mathrm{Gal}(\bar F/F)$ of the elements acting on the residue field
  of $\bar F$ by an integral power of Frobenius, topologized so that the inertia subgroup is open with its profinite
  topology. The reciprocity map gives an isomorphism of $F^\times$ onto $W_F^{\mathrm{ab}}$, sending uniformizers to
  geometric Frobenius elements. For a finite separable extension $E/F$, $W_E$ is an open subgroup of finite index of
  $W_F$, so representations of $W_E$ induce to $W_F$. An unramified representation is one trivial on inertia; an
  unramified semisimple representation of dimension $n$ is determined by the conjugacy class of the image of a
  Frobenius element.
- **Archimedean Weil groups.** $W_{\mathbb{C}} = \mathbb{C}^\times$, and $W_{\mathbb{R}} = \mathbb{C}^\times \cup j\mathbb{C}^\times$ with
  $jzj^{-1} = \bar z$ and $j^2 = -1$, an extension of $\mathrm{Gal}(\mathbb{C}/\mathbb{R})$ by $\mathbb{C}^\times$ with
  $W_{\mathbb{R}}^{\mathrm{ab}} \cong \mathbb{R}^\times$; its irreducible representations have dimension $1$ or $2$.
- **Archimedean local Langlands correspondence for $\mathrm{GL}_n$** (Langlands). For $k = \mathbb{R}$ or $\mathbb{C}$ there is a
  natural bijection $\pi \mapsto \tau(\pi)$ from the irreducible admissible smooth representations of moderate
  growth of $\mathrm{GL}_n(k)$ (equivalently, by Casselman and Wallach, the irreducible admissible
  $(\mathfrak{g}, K)$-modules) onto the $n$-dimensional semisimple representations of $W_k$. Characters of
  $\mathrm{GL}_1(k)$ correspond to characters of $W_k^{\mathrm{ab}} = k^\times$; for $\tau = \bigoplus_i \tau_i$ with
  $\tau_i$ irreducible, $\pi(\tau)$ is the Langlands quotient of the representation induced from the $\pi(\tau_i)$.
- **Factors of pairs.** With $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$ and $\Gamma_{\mathbb{C}}(s) = 2(2\pi)^{-s}\Gamma(s)$, Weil
  attached $L(s, \tau)$ and $\varepsilon(s, \tau, \psi)$ to semisimple representations of $W_k$ (for instance
  $L(s, \lvert \cdot \rvert^r) = \Gamma_k(s + r)$), additively in direct sums, and for representations $\pi$ of
  $\mathrm{GL}_n(k)$ and $\pi'$ of $\mathrm{GL}_m(k)$, $L(s, \pi \times \pi') = L(s, \tau(\pi) \otimes \tau(\pi'))$ and
  $\varepsilon(s, \pi \times \pi', \psi) = \varepsilon(s, \tau(\pi) \otimes \tau(\pi'), \psi)$.

## Expansion

A good expansion has definition pages for the Weil groups of non-archimedean and archimedean local fields and for
unramified parameters, and statement pages for the archimedean local Langlands correspondence for $\mathrm{GL}_n$
and for Weil's archimedean $L$- and $\varepsilon$-factors, each citing the sources below with locators.

## Depends on

- [Local class field theory: the local Artin map](../../NumberTheory/p-adic-numbers/local-class-field-theory.md), for the reciprocity isomorphism
  $F^\times \cong W_F^{\mathrm{ab}}$
- [Admissible representations of real reductive groups](representations-of-real-reductive-groups/admissible-representations-of-real-reductive-groups.md), for the representations of
  $\mathrm{GL}_n(\mathbb{R})$ and $\mathrm{GL}_n(\mathbb{C})$

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): (1.1.6)–(1.1.10) (the Weil group as the inverse image of the integral powers of
  Frobenius, its topology, the alternative definition through Weil classes, and $\mathrm{Art}_K \colon K^\times \cong
  W_K^{\mathrm{ab}}$ sending uniformizers to geometric Frobenius elements).
- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 8, §1, pp. 61–62 (the Weil groups $W_{\mathbb{C}}$ and $W_{\mathbb{R}}$ and the arithmetic Langlands
  classification for $\mathrm{GL}_n(k)$, with Casselman–Wallach), and §2, pp. 62–63 (Weil's $L$- and $\varepsilon$-factors,
  $\Gamma_k$, and the factors of pairs through the classification).
- R. P. Langlands, "On the classification of irreducible representations of real algebraic groups", in
  *Representation theory and harmonic analysis on semisimple Lie groups*, Math. Surveys Monogr. 31, American
  Mathematical Society, 1989, 101–170, the original classification, as cited by Cogdell.
