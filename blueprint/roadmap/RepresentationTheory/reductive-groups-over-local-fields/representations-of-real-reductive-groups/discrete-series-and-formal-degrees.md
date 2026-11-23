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

## Depends on

- [Admissible representations of real reductive groups](admissible-representations-of-real-reductive-groups.md), for irreducible unitary representations and $K$-finite vectors

## Sources

- J. Bernstein and B. Krötz, "Smooth Fréchet globalizations of Harish-Chandra modules", Israel J.
  Math. 199 (2014), 45–111, arXiv:0812.1684 (version 3): §10.2 (square-integrable Harish-Chandra
  modules and the formal degree, equation (10.1), stated for the unitary norm on the
  $K$-finite vectors and the dual norm).
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
  states a related result as `GlobalTheory.Published.SchurOrthogonalitySquareIntegrable`.
