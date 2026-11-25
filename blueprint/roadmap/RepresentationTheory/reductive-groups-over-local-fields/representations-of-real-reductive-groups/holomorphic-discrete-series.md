# Holomorphic discrete series

Let $G$ be a connected reductive Lie group with compact centre and a faithful finite-dimensional
representation, $K$ a maximal compact subgroup, and suppose that $G/K$ carries a Hermitian
symmetric structure, as for $G = \mathrm{U}(p, q)$ and $K = \mathrm{U}(p) \times \mathrm{U}(q)$. Let
$H \subseteq K$ be a compact Cartan subgroup, $\Phi$ the roots of the complexified Lie algebras
$(\mathfrak{g}, \mathfrak{h})$, $\Phi^c$ and $\Phi^n$ the compact and noncompact roots, and
$\Lambda$ the lattice of differentials of characters of $H$.

There is a system of positive roots $\Psi$ such that the sum of two roots in $\Psi \cap \Phi^n$ is
never a root. It gives a splitting $\mathfrak{p} = \mathfrak{p}_+ \oplus \mathfrak{p}_-$ of the
complexified tangent space of $G/K$ into abelian $\mathrm{Ad}\,K$-invariant subalgebras, which
exponentiate in the complexification $G^{\mathbb{C}}$ to unipotent subgroups $P_\pm$; then
$K^{\mathbb{C}} P_+$ is a parabolic subgroup of $G^{\mathbb{C}}$,
$G \cap K^{\mathbb{C}} P_+ = K$, and $G/K$ is an open $G$-orbit in the compact dual
$G^{\mathbb{C}}/K^{\mathbb{C}} P_+$, which gives $G/K$ an invariant complex structure. Let
$\rho$ be half the sum of the roots in $\Psi$, $\rho_c$ and $\rho_n$ half the sums of those in
$\Psi \cap \Phi^c$ and $\Psi \cap \Phi^n$, and let $\lambda$ satisfy $\lambda + \rho \in \Lambda$ and
$(\lambda, \alpha) > 0$ for $\alpha \in \Psi \cap \Phi^c$. Then $\mu = \lambda - \rho_c + \rho_n$ is
the highest weight of an irreducible holomorphic $K^{\mathbb{C}}$-module $V_\mu$, which extends to
$K^{\mathbb{C}} P_+$ and defines a $G$-homogeneous holomorphic vector bundle over $G/K$.

**Theorem (Harish-Chandra).** The space $\mathbf{F}_\lambda$ of holomorphic sections of this bundle
is a Fréchet space on which $G$ acts continuously by translation. Its $K$-finite vectors are
isomorphic, as a $K$-module, to $V_\mu \otimes S(\mathfrak{p}_+)$; in particular $V_\mu$ occurs in
$\mathbf{F}_\lambda$ exactly once, and it lies in every nonzero closed $G$-invariant subspace. If
moreover $(\lambda, \alpha) > 0$ for every $\alpha \in \Psi$, noncompact roots included, then
$\mathbf{F}_\lambda$ is infinitesimally equivalent to a discrete series representation. The
discrete series representations obtained in this way form the **holomorphic discrete series**.

Without the positivity on the noncompact roots, $\mathbf{F}_\lambda$ is still defined, and some of
these modules are not unitarizable.

## Depends on

- [Discrete series representations and formal degrees](discrete-series-and-formal-degrees.md), for square-integrable representations
- [Admissible representations of real reductive groups](admissible-representations-of-real-reductive-groups.md), for $K$-finite vectors

## Proof depends on

- [Harish-Chandra's construction of the holomorphic discrete series](harish-chandra-construction-of-holomorphic-discrete-series.md), for the realization of $G/K$ as a bounded domain in $\mathfrak{p}_-$ through $G \subseteq P_- K^{\mathbb{C}} P_+$, on which the $K$-finite holomorphic sections are the polynomial functions on $\mathfrak{p}_-$, a $K$-module isomorphic to $V_\mu \otimes S(\mathfrak{p}_+)$ by the duality of $\mathfrak{p}_+$ and $\mathfrak{p}_-$ (Schmid, §7, p. 125); for the Fréchet topology; for the lowest $K$-type argument, by evaluation at the base point; and for Harish-Chandra's square-integrability under $(\lambda, \alpha) > 0$ for all $\alpha \in \Psi$
- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for the continuous projection onto the $V_\mu$-isotypic component in the lowest $K$-type argument: a nonzero closed $G$-invariant subspace contains, after translation, a section nonzero at the base point, evaluation there maps its $V_\mu$-isotypic part onto the fibre $V_\mu$, and $V_\mu$ occurs only once in $\mathbf{F}_\lambda$

## Sources

- W. Schmid, "On the characters of the discrete series. The Hermitian symmetric case", Invent.
  Math. 30 (1975), 47–144, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0030>: §3 "The
  'holomorphic discrete series'", (3.1)–(3.9) (the hypotheses on $G$, the ordering $\Psi$, the
  splitting $\mathfrak{p}_\pm$, the embedding of $G/K$ in its compact dual, the module $V_\mu$, the
  $G$-modules $\mathbf{F}_\lambda$ with their $K$-finite vectors, the $K$-type $V_\mu$ lying "in every
  closed, G-invariant subspace", and "Some of the representations are unitary and belong to the
  discrete series, whereas others cannot be unitarized"), and pp. 72–73, (3.12) ("If λ satisfies
  (3.12) $(\lambda, \alpha) > 0$ for all $\alpha \in \Psi$, in addition to (3.7), the G-module
  $\mathbf{F}_\lambda$ belongs to the discrete series [13], up to infinitesimal equivalence, of
  course"), after Harish-Chandra,
  "Representations of semi-simple Lie groups" IV–VI, Amer. J. Math. 77 (1955) and 78 (1956).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a different result for $\mathrm{U}(p, q)$ as `GlobalTheory.Published.HolomorphicDiscreteSeries`:
  for a discrete series representation whose Harish-Chandra parameter lies in the holomorphic
  chamber, every $K$-type has highest weight $\mu$ plus a sum of roots of $\mathfrak{p}_+$,
  $\mathfrak{p}_-$ annihilates the $K$-type $V_\mu$, and the iterated action of $\mathfrak{p}_+$ on
  that $K$-type spans the $K$-finite vectors. The theorem above constructs the modules
  $\mathbf{F}_\lambda$ and does not state this lowest-weight description.
