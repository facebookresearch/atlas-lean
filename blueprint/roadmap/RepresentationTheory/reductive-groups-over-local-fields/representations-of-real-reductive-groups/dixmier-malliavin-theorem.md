# Dixmier–Malliavin theorem

Let $G$ be a Lie group with a left Haar measure $dg$, and for $f, \psi \in C_c^\infty(G)$ let
$(f * \psi)(y) = \int_G f(x)\psi(x^{-1}y) \, dx$.

1. **Functions** (Dixmier–Malliavin, Théorème 3.1). Every $\varphi \in C_c^\infty(G)$ is a finite
   sum $\varphi = f_1 * \psi_1 + \dots + f_N * \psi_N$ with $f_i, \psi_i \in C_c^\infty(G)$, and for a
   neighbourhood $W$ of the identity fixed in advance the factorization can be chosen with
   $\operatorname{supp}(f_i) \subseteq W$ and $\operatorname{supp}(\psi_i) \subseteq \operatorname{supp}(\varphi)$
   for every $i$.
2. **Vectors.** Let $(\pi, V)$ be a continuous representation of $G$ on a Fréchet space $V$. A
   vector $v \in V$ is smooth if $g \mapsto \pi(g)v$ is a smooth map $G \to V$; for
   $f \in C_c^\infty(G)$, $\pi(f)v = \int_G f(g)\pi(g)v \, dg$. Then the smooth vectors of $V$ are
   exactly the finite sums $\sum_i \pi(f_i)v_i$ with $f_i \in C_c^\infty(G)$ and $v_i \in V$: the
   space of smooth vectors is the Gårding subspace. In particular, for a smooth Fréchet
   representation $(\pi, E)$, every vector of $E$ is such a finite sum with $v_i \in E$.

## Depends on

- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for continuous representations of a Lie group on a Fréchet space, smooth vectors and the integrated action $\pi(f)v$ in item 2

## Proof depends on

- [The Dixmier–Malliavin lemma and factorization along one-parameter subgroups](dixmier-malliavin-lemma-and-factorization.md), for both items: the lemma on $\delta$, with convergence in compactly supported distributions and $f, g$ supported in a prescribed neighbourhood of $0$; for item 1, the factorization of functions along flows assembled into kernels on $G$ in product coordinates; for item 2, the separate vector form, with convergence in the seminorms of $V^\infty$

## Sources

- M. Francis, "A Dixmier-Malliavin theorem for Lie groupoids", arXiv:2009.13760 (version 1),
  pp. 1–2, Theorem 1 ("3.1 Théorème, [9]": every $\varphi \in C_c^\infty(G)$ is
  $f_1 * \psi_1 + \dots + f_N * \psi_N$ with $f_i, \psi_i \in C_c^\infty(G)$, and "for every i,
  $\operatorname{supp}(\psi_i) \subseteq \operatorname{supp}(\varphi)$ and $\operatorname{supp}(f_i) \subseteq W$, where
  $W \subseteq G$ is a neighbourhood of the identity fixed in advance"), for item 1, citing
  J. Dixmier and P. Malliavin, "Factorisations de fonctions et de vecteurs indéfiniment
  différentiables", Bull. Sci. Math. (2) 102 (1978), 307–330, Théorème 3.1.
- W. Casselman, "Canonical extensions of Harish-Chandra modules to representations of G", Canad. J.
  Math. 41 (1989), 385–438, <https://doi.org/10.4153/CJM-1989-019-5>: §1 ("the strong main result
  [15, Théorème 3.3], according to which in any Fréchet space on which G acts continuously the
  spaces $V^{\mathrm{sm}}$ and the Gårding subspace coincide", the Gårding subspace being spanned by
  the vectors $\pi(f)v$ with $f \in C_c^\infty(G)$), where [15] is J. Dixmier and P. Malliavin,
  "Factorisations de fonctions et de vecteurs indéfiniment différentiables", Bull. Sci. Math. (2)
  102 (1978), 307–330; for item 2.
- J. Bernstein and B. Krötz, "Smooth Fréchet globalizations of Harish-Chandra modules", Israel J.
  Math. 199 (2014), 45–111, arXiv:0812.1684 (version 3): Remark 2.19 ("If $(\pi, E)$ is a smooth
  Fréchet-representation, then $\Pi(C_c^\infty(G))E = E$ by Dixmier–Malliavin").
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states item 1 as `GlobalTheory.Published.DixmierMalliavinLie` and, for closed subgroups of
  $\mathrm{GL}_n(\mathbb{C})$, as `GlobalTheory.Published.DixmierMalliavinFactorisation`.
