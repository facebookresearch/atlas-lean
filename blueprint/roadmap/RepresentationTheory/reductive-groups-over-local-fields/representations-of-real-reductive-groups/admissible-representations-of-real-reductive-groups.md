# Admissible representations of real reductive groups

Let $G$ be the group of real points of a Zariski-connected reductive algebraic group over
$\mathbb{R}$, such as $\mathrm{U}(p, q)$, and $K$ a maximal compact subgroup, such as
$\mathrm{U}(p) \times \mathrm{U}(q)$. A continuous representation $(\pi, V)$ of $G$ on a complete
locally convex Hausdorff space $V$ has **smooth vectors** $v$, those for which $g \mapsto \pi(g)v$
is smooth, and **$K$-finite vectors**, those contained in a finite-dimensional $K$-stable subspace;
$V_K$ denotes the space of $K$-finite vectors. The representation is **admissible**, or has finite
$K$-multiplicities, if every irreducible representation of $K$ occurs in $V$ with finite
multiplicity.

1. **Harish-Chandra's admissibility theorem.** Every irreducible unitary representation of $G$ is
   admissible. For $G$ connected semisimple with finite centre, each irreducible representation
   $V_i$ of $K$ occurs in it with multiplicity at most $\dim V_i$.
2. If $(\pi, V)$ is a continuous admissible representation, then every $K$-finite vector is
   smooth, $V_K$ is stable under $K$ and under the action of the complexified Lie algebra
   $\mathfrak{g}$ of $G$ on smooth vectors, and every $K$-finite linear form on $V_K$ extends
   uniquely to a continuous $K$-finite linear form on $V$. For every continuous representation on
   a Fréchet space, the smooth $K$-finite vectors are dense; so for admissible $V$, $V_K$ is dense
   in $V$.

## Depends on

- [Linear algebraic groups over local fields and their groups of rational points](../linear-algebraic-groups-over-local-fields.md), for the real points of a Zariski-connected reductive group over $\mathbb{R}$ as a Lie group and for its maximal compact subgroups
- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for the action of the complexified Lie algebra on smooth vectors in item 2

## Proof depends on

- [Proof of Harish-Chandra's admissibility theorem](proof-of-harish-chandra-admissibility-theorem.md), for item 1, which the sources cited here quote without proof
- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for item 2: the smooth vectors are dense (Dirac sequences on $G$), the isotypic projections are continuous and preserve smoothness, and the $K$-finite vectors are dense; for admissible $V$ each isotypic component is finite-dimensional and contains the dense image of the smooth vectors, so it consists of smooth vectors, and a $K$-finite linear form on $V_K$ extends uniquely by composing with the continuous projection onto finitely many isotypic components
- [Peter–Weyl theorem: unitary representations separate points](../../lie-and-topological-representations/representations-of-compact-groups/peter-weyl-point-separation.md), for the density of the $K$-finite vectors in item 2: through the complex Stone–Weierstrass theorem it makes the matrix coefficients of finite-dimensional representations of $K$ dense in $C(K)$, which with a Dirac sequence on $K$ gives the density

## Sources

- W. Casselman, "Canonical extensions of Harish-Chandra modules to representations of G", Canad. J.
  Math. 41 (1989), 385–438, <https://doi.org/10.4153/CJM-1989-019-5>: introduction (the class of
  groups), §1 (smooth and $K$-finite vectors; "The intersection $V^{\mathrm{sm}} \cap V_K$ is dense
  in V and stable under both g and K"), §2 (condition (H1)), Proposition 2.2 (a)–(b)
  (item 2) and the remark after it ("It is a result of Harish-Chandra that if $\pi$ is irreducible
  and unitary then it satisfies (H1)").
- J. Bernstein and B. Krötz, "Smooth Fréchet globalizations of Harish-Chandra modules", Israel J.
  Math. 199 (2014), 45–111, arXiv:0812.1684 (version 3): Remark 5.1 ("if $(\pi, H)$ happens to be a
  unitary irreducible representation, then Harish-Chandra has shown that $\pi$ is admissible").
- M. F. Atiyah and W. Schmid, "A geometric construction of the discrete series for semisimple Lie
  groups", Invent. Math. 42 (1977), 1–62, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0042>:
  §2, (2.1) (the bound $n_i \le \dim V_i$ for connected real semisimple Lie groups with finite
  centre).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a related result as `GlobalTheory.Published.KFiniteVectorsUnitary`.
