# Representations of U(p, q)

This node covers the representation theory of real reductive groups that the archimedean places of
unitary groups need, chiefly $G = \mathrm{U}(p, q)$ with maximal compact subgroup
$K = \mathrm{U}(p) \times \mathrm{U}(q)$. In general $G$ is a linear reductive group with maximal
compact subgroup $K$, Lie algebra $\mathfrak{g}$ and centre $Z(\mathfrak{g})$ of the enveloping
algebra.

- **Admissibility** (Harish-Chandra). Every irreducible unitary representation of $G$ is admissible:
  each irreducible representation of $K$ occurs in it with finite multiplicity. In a continuous
  representation with finite $K$-multiplicities every $K$-finite vector is smooth; if its $K$-finite
  vectors form a Harish-Chandra module, their matrix coefficients against $K$-finite linear
  functionals are analytic.
- **Harish-Chandra modules.** A $(\mathfrak{g}, K)$-module is a $\mathfrak{g}$-module with a
  compatible action of $K$ for which every vector is $K$-finite; a Harish-Chandra module is a
  finitely generated $(\mathfrak{g}, K)$-module with finite $K$-multiplicities, equivalently one with
  finite $K$-multiplicities that is $Z(\mathfrak{g})$-finite, or of finite length. For a
  continuous representation with finite $K$-multiplicities, taking closures is a bijection from the
  $(\mathfrak{g}, K)$-submodules of its $K$-finite vectors onto its closed $G$-stable subspaces; in
  particular the representation is irreducible exactly when its $(\mathfrak{g}, K)$-module of
  $K$-finite vectors is.
- **Casselman–Wallach globalization.** Every Harish-Chandra module is, up to canonical topological
  isomorphism, the module of $K$-finite vectors of exactly one smooth representation of $G$ of
  moderate growth on a Fréchet space, and this assignment is functorial and exact. Equivalently,
  taking $K$-finite vectors is an equivalence from the category of smooth admissible Fréchet
  representations of moderate growth and finite length (those whose $K$-finite vectors form a
  Harish-Chandra module) onto the category of Harish-Chandra modules.
- **Dixmier–Malliavin.** For a continuous representation of a Lie group $G$ on a Fréchet space $V$,
  the smooth vectors are exactly the finite sums of vectors $\pi(f)v$ with
  $f \in C_c^\infty(G)$ and $v \in V$.
- **Discrete series** (Harish-Chandra). An irreducible unitary representation whose matrix
  coefficients are square-integrable lies in the discrete series and has a formal degree. Let $G$ be
  connected semisimple. Then $G$ has a discrete series if and only if $G$ and $K$ have the same
  rank (the dimension of a Cartan subalgebra of their complexified Lie algebras), that is, if and
  only if $G$ has a compact Cartan subgroup. Let $H \subset K$ be a compact Cartan subgroup, with Lie
  algebra $\mathfrak{h}_0$, let $\Lambda \subset i\mathfrak{h}_0^*$ be the lattice of differentials
  of characters of $H$, and let $\rho_0$ be half the sum of the positive roots for some ordering of
  $i\mathfrak{h}_0^*$; the translate $\Lambda + \rho_0$ does not depend on the ordering. Every
  nonsingular $\lambda \in \Lambda + \rho_0$ gives an invariant eigendistribution $\Theta_\lambda$;
  each $\Theta_\lambda$ is the character of a discrete series representation $\pi_\lambda$, every
  discrete series representation arises in this way, and $\Theta_{\lambda_1} = \Theta_{\lambda_2}$ exactly when
  $\lambda_1$ and $\lambda_2$ are conjugate under the Weyl group $W$ of $(G, H)$, which is also the
  Weyl group of $(K, H)$. The formal degree of $\pi_\lambda$ is a constant multiple of
  $\lvert \prod_{\alpha > 0} \langle \lambda, \alpha \rangle \rvert$. The diagonal matrices in
  $\mathrm{U}(p) \times \mathrm{U}(q)$ form a compact Cartan subgroup of $\mathrm{U}(p, q)$.
- **Blattner's formula** (Hecht–Schmid). Suppose $G$ has a faithful finite-dimensional
  representation. Let $\Psi$ be the system of roots $\alpha$ with $(\alpha, \lambda) > 0$, let
  $\rho_c$ and $\rho_n$ be half the sums of the compact and of the noncompact roots in $\Psi$, and
  let $Q(\mu)$ be the number of ways of writing $\mu$ as a sum of noncompact roots in $\Psi$. If
  $\mu \in \Lambda$ is dominant for the compact roots in $\Psi$, the irreducible $K$-module of highest
  weight $\mu$ with respect to these roots occurs in $\pi_\lambda$ with multiplicity
  $\sum_{w \in W} \varepsilon(w)\, Q(w(\mu + \rho_c) - \lambda - \rho_n)$. Schmid had shown that this
  is an upper bound, and that discrete series representations are characterized, up to
  infinitesimal equivalence, by their restrictions to $K$.
- **Holomorphic discrete series.** If $G$ is connected reductive with compact centre and a
  faithful finite-dimensional representation, and $G/K$ is Hermitian symmetric, as for
  $\mathrm{U}(p, q)$, then Harish-Chandra constructs representations of $G$ on spaces of holomorphic
  sections of homogeneous holomorphic vector bundles over $G/K$, which is an open $G$-orbit in its
  compact dual; the square-integrable ones form the holomorphic discrete series.

Smooth representations of $p$-adic groups and the Weil representation are outside this node.

## Expansion

A good expansion replaces this node by definition pages and statements in the following order,
each citing the source and locator below. It builds on
[Representations of topological and Lie groups](../lie-and-topological-representations/README.md).

1. Admissible representations, smooth and $K$-finite vectors, the Dixmier–Malliavin theorem, and
   Harish-Chandra's admissibility theorem for irreducible unitary representations.
2. $(\mathfrak{g}, K)$-modules and Harish-Chandra modules, with the correspondence between closed
   invariant subspaces and submodules.
3. Representations of moderate growth and the Casselman–Wallach globalization theorem, which uses
   steps 1 and 2.
4. The discrete series: square-integrability, formal degrees, Harish-Chandra's existence criterion
   and parametrization, and Blattner's formula.
5. Hermitian symmetric spaces, the holomorphic discrete series, and the case of $\mathrm{U}(p, q)$.

## Sources

- W. Casselman, "Canonical extensions of Harish-Chandra modules to representations of G", Canad. J.
  Math. 41 (1989), 385–438, <https://doi.org/10.4153/CJM-1989-019-5>: introduction (moderate growth
  and the globalization theorem), §1 (the Dixmier–Malliavin theorem, from J. Dixmier and
  P. Malliavin, Bull. Sci. Math. (2) 102 (1978), 307–330), §2, conditions (C1)–(C4) and (H1)–(H4)
  with Propositions 2.1 and 2.2 ($(\mathfrak{g}, K)$-modules, Harish-Chandra modules, closed
  invariant subspaces, Harish-Chandra's admissibility theorem), §3 (analytic matrix coefficients of
  Harish-Chandra modules), Theorem 10.4 and Corollaries 10.5–10.6.
- J. Bernstein and B. Krötz, "Smooth Fréchet globalizations of Harish-Chandra modules", Israel J.
  Math. 199 (2014), 45–111, arXiv:0812.1684 (version 3): §1 (Harish-Chandra modules, smooth
  admissible Fréchet globalizations of moderate growth, and the Casselman–Wallach theorem, credited
  to Casselman and to N. R. Wallach), Remark 2.19
  (Dixmier–Malliavin), Remark 5.1 (admissibility), §10.2 and Theorem 10.6.
- Harish-Chandra, "Discrete series for semisimple Lie groups. II. Explicit determination of the
  characters", Acta Math. 116 (1966), 1–111, <https://doi.org/10.1007/BF02392813>: §1, §37 (discrete
  series and formal degree), Theorem 13 (existence criterion) and Theorem 16 (characters,
  parametrization and formal degrees); from §39 on Harish-Chandra assumes $G$ acceptable.
- H. Hecht and W. Schmid, "A proof of Blattner's conjecture", Invent. Math. 31 (1975), 129–154,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0031>: §1, (1.1)–(1.2) and Theorem (1.3)
  (existence of the discrete series exactly when $G$ has a compact Cartan subgroup, $\rho_0$ and the
  parameters of the discrete series, Blattner's formula with $\mu$ dominant for the compact roots in
  $\Psi$, Schmid's earlier results).
- W. Schmid, "On the characters of the discrete series. The Hermitian symmetric case", Invent.
  Math. 30 (1975), 47–144, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0030>: §3 "The
  'holomorphic discrete series'" (Harish-Chandra's construction in Representations of semi-simple
  Lie groups IV–VI, Amer. J. Math. 77 (1955) and 78 (1956)).
- A. W. Knapp, *Representation Theory of Semisimple Groups: an Overview Based on Examples*,
  Princeton University Press, 1986: Chapters VI "Holomorphic discrete series" (pp. 150–166), VIII
  "Admissible representations" (pp. 203–280) and IX "Construction of discrete series"
  (pp. 281–332).
- Proof of the Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet
  L-functions: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>).
  Statement and proof of the Riemann hypothesis certified by the Lean and Mathlib communities in a
  joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative
  (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); independent checks of
  its five main theorems by A. Sutherland (<https://math.mit.edu/~drew/grh/>). Source mirror:
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
  The library has no licence, so none of its Lean comes into ATLAS; ATLAS has no Lean proof of
  its own. Related formal statements in Alpöge's proof, often in specialised forms,
  include `GlobalTheory.Published.KFiniteVectorsUnitary`,
  `GlobalTheory.Published.HarishChandraModules`, `GlobalTheory.Published.GKGlobalisation`,
  `GlobalTheory.Published.CasselmanWallach`, `GlobalTheory.Published.DixmierMalliavinFactorisation`,
  `GlobalTheory.Published.SchurOrthogonalitySquareIntegrable`,
  `GlobalTheory.Published.DiscreteSeriesUpqExists` and
  `GlobalTheory.Published.HolomorphicDiscreteSeries`.
