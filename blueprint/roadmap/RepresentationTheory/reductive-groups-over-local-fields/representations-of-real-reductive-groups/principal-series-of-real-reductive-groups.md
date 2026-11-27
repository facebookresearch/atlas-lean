# Characters, principal series and the Langlands classification for real reductive groups

This node is still to be broken down. It covers the parts of Harish-Chandra's theory of real
reductive groups, and of its continuation by Langlands, Casselman and Wallach, that the proofs of
the statements on [Harish-Chandra modules](harish-chandra-modules.md), the
[Casselman–Wallach globalization theorem](casselman-wallach-globalization.md), the
[classification of the discrete series](harish-chandra-discrete-series-classification.md) and
[Blattner's formula](blattner-formula.md) use, for $G$ the group of real points of a
Zariski-connected reductive algebraic group over $\mathbb{R}$ with maximal compact subgroup $K$,
and, for the results that Atiyah and Schmid use in the theory of the discrete series, for every
connected semisimple Lie group with finite centre, linear or not.

- **Characters.** The distribution character $f \mapsto \operatorname{trace} \pi(f)$ of an
  irreducible unitary representation, or more generally of an admissible representation of finite
  length on a Hilbert space, whose operators $\pi(f)$, $f \in C_c^\infty(G)$, are of trace class
  (finite $K$-multiplicities alone do not suffice: on $\mathrm{U}(1)$, the weights $n \ge 1$ with
  multiplicities $2^n$ and a test function with Fourier coefficients $2^{-n}$ give no trace);
  invariant eigendistributions,
  Harish-Chandra's regularity theorem (local integrability and analyticity on the regular set),
  the matching conditions between Cartan subgroups, the notion of an invariant eigendistribution
  bounded at infinity, and the Plancherel theorem; the formula for the product of a discrete series
  character with a finite-dimensional character, and the characters of the modules
  $\mathbf{F}_\lambda$ of the Hermitian symmetric case.
- **Principal series.** Representations induced from parabolic subgroups, $K$-finite and smooth;
  the $\mathfrak{n}$-homology of Harish-Chandra modules and Casselman's subrepresentation theorem
  (every Harish-Chandra module embeds, as a $(\mathfrak{g}, K)$-module, in the $K$-finite vectors
  of the representation induced from some finite-dimensional representation of a minimal parabolic
  subgroup $P_{\min}$); Wallach's automatic continuity theorem; analytic families of principal
  series and their intertwining operators.
- **The Langlands classification** of irreducible Harish-Chandra modules by essentially tempered
  representations of Levi subgroups, with the reduction of tempered to square-integrable
  representations.
- **The Atiyah–Schmid construction** of the discrete series of a connected semisimple Lie group
  with finite centre, not necessarily linear, through the $L^2$-index theory of Dirac operators
  on $G/K$, and Zuckerman's tensoring with finite-dimensional representations, with which Atiyah
  and Schmid prove Harish-Chandra's theorem and the lowest $K$-type theorem.

## Expansion

A good expansion has definition pages for distribution characters, invariant eigendistributions
and principal series, and statement pages for the regularity theorem, the matching conditions, the
Plancherel theorem, Casselman's subrepresentation theorem, the automatic continuity theorem, the
Langlands classification, the character identities used by Hecht and Schmid and the steps of the
Atiyah–Schmid construction, each citing the sources below with locators.

It also writes out these steps of its own proof:

- Atiyah and Schmid's application of these to the Dirac operators on $G/K$ in §3 (p. 8), whose output §§4–5 then use, for the Atiyah–Schmid construction.

## Depends on

- [Admissible representations of real reductive groups](admissible-representations-of-real-reductive-groups.md), for admissible and irreducible unitary representations and their smooth and $K$-finite vectors
- [Discrete series representations and formal degrees](discrete-series-and-formal-degrees.md), for discrete series and square-integrable representations (square-integrability modulo the centre is not membership in $L^2(G)$ when the centre is noncompact)
- [Holomorphic discrete series](holomorphic-discrete-series.md), for the modules $\mathbf{F}_\lambda$ of the Hermitian symmetric case, whose characters the first item uses
- [Linear algebraic groups over local fields and their groups of rational points](../linear-algebraic-groups-over-local-fields.md), for the real points of Zariski-connected reductive groups and their maximal compact subgroups
- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for the parabolic $\mathbb{R}$-subgroups $P = MN$ of the algebraic group and their Levi decompositions, over $k = \mathbb{R}$
- [Iwasawa and Langlands decompositions of real reductive groups](iwasawa-and-langlands-decompositions.md), for the Langlands decompositions $P = MAN$ of real parabolic subgroups and Cartan subgroups, also for connected semisimple Lie groups with finite centre that are not linear, for the principal series and the characters
- [Spectral theorem for unbounded self-adjoint operators, and trace-class operators](../../../Analysis/operator-theory/spectral-theory/unbounded-self-adjoint-and-trace-class-operators.md), for trace-class operators on a Hilbert space and the trace of $\pi(f)$, $f \in C_c^\infty(G)$, for distribution characters
- [(g, K)-modules, the centre of the enveloping algebra and Harish-Chandra's homomorphism](g-k-modules-and-harish-chandra-homomorphism.md), for the definition of Harish-Chandra modules, used by the second and third items

## Proof depends on

- [Admissible representations of real reductive groups](admissible-representations-of-real-reductive-groups.md), for the bound $n_i \le \dim V_i$ on $K$-multiplicities of irreducible unitary representations in the connected semisimple case, through which Atiyah and Schmid show that the operators $\pi(f)$ are of trace class (Atiyah–Schmid, §2, (2.1)); for nonlinear groups with finite centre they cite the bound directly
- [Peter–Weyl theorem: unitary representations separate points](../../lie-and-topological-representations/representations-of-compact-groups/peter-weyl-point-separation.md), for point separation, from which the density of matrix coefficients of $K$ follows by the Stone–Weierstrass theorem
- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for the decomposition into $K$-types used throughout: the continuous isotypic projections and, for unitary representations, the Hilbert direct sum of the isotypic components
- [Atiyah's L²-index theorem and cocompact lattices of semisimple groups](atiyah-l2-index-theorem-and-cocompact-lattices.md), for Atiyah's $L^2$-index theorem for an elliptic operator on a manifold with a free, properly discontinuous and cocompact action of a discrete group, the index theorem on the compact quotient, and Borel's existence of cocompact torsion-free discrete subgroups of connected semisimple groups with finite centre, for the Atiyah–Schmid construction

## Sources

- W. Casselman, "Canonical extensions of Harish-Chandra modules to representations of G", Canad. J.
  Math. 41 (1989), 385–438, <https://doi.org/10.4153/CJM-1989-019-5>: §4 (representations induced
  from parabolic subgroups and the Langlands classification, Propositions 4.5–4.9), §5
  (completions with respect to $\mathfrak{n}$, Corollaries 5.7–5.8), §7 (functorial extensions
  attached to principal series embeddings, with Wallach's results), §9 (analytic families).
- J. Bernstein and B. Krötz, "Smooth Fréchet globalizations of Harish-Chandra modules", Israel J.
  Math. 199 (2014), 45–111, arXiv:0812.1684 (version 3): §1 (Casselman's subrepresentation
  theorem), Theorem 4.4 (Casselman: "For every Harish-Chandra module V there exists a finite
  dimensional $P_{\min}$-module W and a $(\mathfrak{g}, K)$-embedding $V \to I(W)$"), §§8–10 (minimal principal series, deformations and the Langlands classification in the
  proof of Theorem 10.6).
- M. F. Atiyah and W. Schmid, "A geometric construction of the discrete series for semisimple Lie
  groups", Invent. Math. 42 (1977), 1–62, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0042>:
  §1 (the results assumed, (a)–(k): Harish-Chandra characters, the structure of bi-invariant
  differential operators, local integrability), §2 (the Plancherel theorem and characters),
  Lemma (6.3) (trace class operators $\pi(f)$ for discrete series representations),
  §3, p. 8 (the $L^2$-index theorem of Atiyah applied to $G/K$), §§4–5 (the construction by Dirac operators), §§6–7 (characters bounded at infinity and the
  matching conditions), §8 (Zuckerman's method; pp. 42–43: infinitesimal equivalence, and the
  characters of admissible representations with a finite composition series).
- H. Hecht and W. Schmid, "A proof of Blattner's conjecture", Invent. Math. 31 (1975), 129–154,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0031>: §1 (the product formula of characters
  and the dependence on Schmid's Hermitian symmetric paper).
- W. Schmid, "On the characters of the discrete series. The Hermitian symmetric case", Invent.
  Math. 30 (1975), 47–144, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0030>: §§3–6 (the
  characters $\Theta(\Psi, \lambda)$ of the modules $\mathbf{F}_\lambda$ and the main theorems).
