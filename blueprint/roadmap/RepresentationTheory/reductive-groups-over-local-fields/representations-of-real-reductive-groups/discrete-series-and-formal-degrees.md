# Discrete series representations and formal degrees

Let $G$ be the group of real points of a Zariski-connected reductive algebraic group over
$\mathbb{R}$, with centre $Z$ and a maximal compact subgroup $K$. An irreducible unitary
representation $(\pi, H)$ of $G$ with a unitary central character is **square-integrable**, or
belongs to the **discrete series**, if for all $K$-finite vectors $v, w \in H$ the matrix
coefficient $g \mapsto \langle \pi(g)v, w \rangle$ satisfies
$\int_{G/Z} \lvert \langle \pi(g)v, w \rangle \rvert^2 \, d(gZ) < \infty$. Then there is a constant
$d(\pi) > 0$, the **formal degree** of $\pi$, depending on the choice of Haar measure on $G/Z$,
such that

$$\int_{G/Z} \lvert \langle \pi(g)v, w \rangle \rvert^2 \, d(gZ) = \frac{\lVert v \rVert^2 \, \lVert w \rVert^2}{d(\pi)}$$

for all $K$-finite $v, w \in H$. For connected semisimple groups, Schmid and Atiyah–Schmid
describe the discrete series as the irreducible unitary representations that can be realized on
invariant subspaces of the left regular representation on $L^2(G)$.

More generally (Godement), let $\pi$ and $\pi'$ be square-integrable irreducible unitary
representations of a unimodular locally compact group $G$, that is, irreducible subrepresentations
of the left regular representation on $L^2(G)$. Then for all vectors $\xi, \eta$ of $\pi$ and
$\xi', \eta'$ of $\pi'$,

$$\int_G \langle \pi(g)\xi, \eta \rangle \, \overline{\langle \pi'(g)\xi', \eta' \rangle} \, dg =
\begin{cases} 0 & \text{if } \pi \not\cong \pi', \\ d_\pi^{-1} \langle \xi, \xi' \rangle \overline{\langle \eta, \eta' \rangle} & \text{if } \pi = \pi', \end{cases}$$

with a constant $d_\pi > 0$, the formal degree, depending on the Haar measure (inner products are
linear in the first variable). Here $\pi = \pi'$ means the same representation on the same space;
if $\pi'$ is only equivalent to $\pi$, through a unitary intertwiner $T$ from the space of $\pi$ to
that of $\pi'$, the second case applies after replacing $\xi'$ and $\eta'$ by $T^{-1}\xi'$ and
$T^{-1}\eta'$. An irreducible unitary representation is square-integrable in this sense as soon as
one matrix coefficient $g \mapsto \langle v, \pi(g)v \rangle$ with $v \ne 0$ is square-integrable.

When the centre $Z$ of $G$ is compact, as for $\mathrm{U}(p, q)$, give $Z$ the Haar measure of total
mass one and $G/Z$ the quotient measure. A function on $G$ invariant under $Z$, such as the absolute
square $\lvert \langle \pi(g)v, w \rangle \rvert^2$ of a matrix coefficient of a representation with a
unitary central character, then has the same integral over $G$ and over $G/Z$; so for such groups
the two definitions of square-integrability and of the formal degree agree. The relations for
two different representations, whose integrands need not be invariant under $Z$, are taken over $G$.

## Depends on

- [Admissible representations of real reductive groups](admissible-representations-of-real-reductive-groups.md), for irreducible unitary representations and $K$-finite vectors

## Proof depends on

- [Coefficient maps of square-integrable representations](../../lie-and-topological-representations/coefficients-of-square-integrable-representations.md), for the square-integrability of all coefficients once one diagonal coefficient is square-integrable, and for the boundedness of the coefficient maps $T_\eta \colon \xi \mapsto \langle \pi(\cdot)\xi, \eta \rangle$ into $L^2(G)$, which intertwine $\pi$ with the right regular representation; also for the inversion on an arbitrary unimodular group in Godement's general statement
- [Spectral theorem for bounded self-adjoint operators, multiplication form](../../../Analysis/operator-theory/spectral-theory/spectral-theorem-for-bounded-self-adjoint-operat/bounded-self-adjoint-spectral-multiplica.md), for Schur's lemma for irreducible unitary representations: a bounded operator commuting with $\pi$ is a scalar, applied to $T_\eta^* T_{\eta'}$, which commutes with $\pi$ since both maps intertwine $\pi$ with the right regular representation (it need not be positive: for $\eta' = -\eta$ it is $-T_\eta^* T_\eta$); and a bounded intertwiner between inequivalent irreducible unitary representations vanishes, which gives the two cases of the relations
- [Right-invariant Haar measures are inversion-invariant](../../../MeasureTheory/haar-measure/unimodular-groups/is-inv-invariant-of-is-mul-right-invaria.md), for unimodular $G$ in the second-countable case, which covers the Lie groups of the first paragraph: $\langle \pi(g^{-1})\xi, \eta \rangle = \overline{\langle \pi(g)\eta, \xi \rangle}$ and the invariance of $dg$ under inversion exchange the roles of the two vectors
- [Integration over quotients of locally compact groups](../../../MeasureTheory/haar-measure/integration-over-quotients-of-locally-compact-groups.md), for $\int_G = \int_{G/Z}$ on functions invariant under a compact centre $Z$ with Haar measure of mass one, which is what the compact-centre paragraph uses; nothing is claimed for a noncompact centre

## Sources

- J. Bernstein and B. Krötz, "Smooth Fréchet globalizations of Harish-Chandra modules", Israel J.
  Math. 199 (2014), 45–111, arXiv:0812.1684 (version 3): §10.2 (square-integrable Harish-Chandra
  modules and the formal degree, equation (10.1), stated for the unitary norm on the
  $K$-finite vectors and the dual norm).
- A. I. Shtern, "Integrable representation", *Encyclopedia of Mathematics*,
  <http://encyclopediaofmath.org/index.php?title=Integrable_representation&oldid=51797>: the
  orthogonality relations for square-integrable representations of locally compact unimodular
  groups for all vectors, the formal degree, and the square-integrable representations as the
  irreducible subrepresentations of the regular representation (citing G. Warner, *Harmonic analysis
  on semi-simple Lie groups* I, Springer, 1972, §4.5.9, and S. A. Gaal, *Linear analysis and
  representation theory*, Springer, 1973, Chapter VII).
- A. L. Carey, "Square-integrable representations of non-unimodular groups", Bull. Austral. Math.
  Soc. 15 (1976), 1–12, <https://doi.org/10.1017/S0004972700036728>: §1 (Godement's and Dixmier's
  orthogonality relations in the unimodular case) and §2 (an irreducible representation is square
  integrable "if there exists a vector v ∈ H such that the coefficient function x ↦ ⟨v, π(x)v⟩ is
  square integrable"; such representations are the irreducible subrepresentations of the left
  regular representation, "as in the unimodular case").
- W. Schmid, "On the characters of the discrete series. The Hermitian symmetric case", Invent.
  Math. 30 (1975), 47–144, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0030>: §1, first
  paragraph (square-integrable representations of a locally compact unimodular group as those
  realizable on an invariant subspace of the left regular representation, and the discrete
  series).
- M. F. Atiyah and W. Schmid, "A geometric construction of the discrete series for semisimple Lie
  groups", Invent. Math. 42 (1977), 1–62, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0042>:
  §1 (the irreducible representations entering the discrete part of $L^2(G)$ are "(by definition)
  those of the discrete series").
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a different result as `GlobalTheory.Published.SchurOrthogonalitySquareIntegrable`: for
  an irreducible unitary representation of a locally compact group with a right-invariant Haar
  measure, if one matrix coefficient of nonzero vectors is square-integrable on the group, then all
  are, and $\int \langle w, \pi(g)v \rangle \overline{\langle w', \pi(g)v' \rangle}\, dg =
  \langle v', v \rangle \langle w, w' \rangle / d$ for all vectors $v, w, v', w'$ (the Schur
  orthogonality relations). The relations above give the same conclusion; the library's hypothesis,
  a single square-integrable coefficient $\langle w_0, \pi(g)v_0 \rangle$ with $v_0, w_0 \ne 0$, is
  more general than the diagonal coefficient in the criterion above.
