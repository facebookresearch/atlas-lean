# Dixmier–Malliavin theorem

Let $G$ be a Lie group and $(\pi, V)$ a continuous representation of $G$ on a Fréchet space $V$.
A vector $v \in V$ is smooth if $g \mapsto \pi(g)v$ is a smooth map $G \to V$; for
$f \in C_c^\infty(G)$ and a Haar measure $dg$, $\pi(f)v = \int_G f(g)\pi(g)v \, dg$. Then the
smooth vectors of $V$ are exactly the finite sums $\sum_i \pi(f_i)v_i$ with $f_i \in C_c^\infty(G)$
and $v_i \in V$: the space of smooth vectors is the Gårding subspace. In particular, for a smooth
Fréchet representation $(\pi, E)$, every vector of $E$ is such a finite sum with $v_i \in E$.

## Sources

- W. Casselman, "Canonical extensions of Harish-Chandra modules to representations of G", Canad. J.
  Math. 41 (1989), 385–438, <https://doi.org/10.4153/CJM-1989-019-5>: §1 ("the strong main result
  [15, Théorème 3.3], according to which in any Fréchet space on which G acts continuously the
  spaces $V^{\mathrm{sm}}$ and the Gårding subspace coincide", the Gårding subspace being spanned by
  the vectors $\pi(f)v$ with $f \in C_c^\infty(G)$), where [15] is J. Dixmier and P. Malliavin,
  "Factorisations de fonctions et de vecteurs indéfiniment différentiables", Bull. Sci. Math. (2)
  102 (1978), 307–330.
- J. Bernstein and B. Krötz, "Smooth Fréchet globalizations of Harish-Chandra modules", Israel J.
  Math. 199 (2014), 45–111, arXiv:0812.1684 (version 3): Remark 2.19 ("If $(\pi, E)$ is a smooth
  Fréchet-representation, then $\Pi(C_c^\infty(G))E = E$ by Dixmier–Malliavin").
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a form of this theorem as `GlobalTheory.Published.DixmierMalliavinFactorisation`.
