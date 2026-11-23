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
$\mathbf{F}_\lambda$ exactly once, and it lies in every closed $G$-invariant subspace. Those
$\mathbf{F}_\lambda$ that are, up to infinitesimal equivalence, square-integrable form the
**holomorphic discrete series**.

## Depends on

- [Discrete series representations and formal degrees](discrete-series-and-formal-degrees.md), for square-integrable representations
- [Admissible representations of real reductive groups](admissible-representations-of-real-reductive-groups.md), for $K$-finite vectors

## Sources

- W. Schmid, "On the characters of the discrete series. The Hermitian symmetric case", Invent.
  Math. 30 (1975), 47–144, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0030>: §3 "The
  'holomorphic discrete series'", (3.1)–(3.9) (the hypotheses on $G$, the ordering $\Psi$, the
  splitting $\mathfrak{p}_\pm$, the embedding of $G/K$ in its compact dual, the module $V_\mu$, the
  $G$-modules $\mathbf{F}_\lambda$ with their $K$-finite vectors, and "The class of
  square-integrable representations among these is often referred to, somewhat informally, as the
  holomorphic discrete series"), after Harish-Chandra, "Representations of semi-simple Lie groups"
  IV–VI, Amer. J. Math. 77 (1955) and 78 (1956).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a related result as `GlobalTheory.Published.HolomorphicDiscreteSeries`.
