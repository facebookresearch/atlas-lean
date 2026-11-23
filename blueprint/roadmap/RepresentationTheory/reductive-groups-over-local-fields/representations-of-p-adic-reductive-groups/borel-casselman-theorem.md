# Borel–Casselman theorem on Iwahori-fixed vectors

Let $F$ be a non-archimedean local field and $G = \mathbf{G}(F)$ for a connected reductive group
$\mathbf{G}$ over $F$. Let $P$ be a minimal parabolic subgroup with unipotent radical $N$, $A$ a
maximal split torus in $P$, $M$ its centralizer (a Levi subgroup of $P$) and $M_0$ the maximal
compact open subgroup of $M$. A character $\chi$ of $M$ is **unramified** if it is trivial on $M_0$,
and the **unramified principal series** $I(\chi)$ is the normalized parabolic induction of $\chi$:
$G$ acts by right translation on the locally constant functions $\phi$ on $G$ with
$\phi(pg) = \chi\delta_P^{1/2}(p)\phi(g)$ for $p \in P$, $g \in G$. Let $C$ be the chamber of the
apartment of $A$ in the Bruhat–Tits building that has a chosen special point as a vertex and lies
in the vectorial chamber determined by $P$, and let $B$ be the Iwahori subgroup fixing $C$ in the
sense of Casselman (1980, §1). It has the Iwahori factorization $B = N_1^- M_0 N_0$ with
$N_1^- \subseteq \bar N$, $N_0 \subseteq N$, where $\bar N$ is the unipotent radical of the opposite
parabolic subgroup; in particular $B \cap M = M_0$, and this convention is used throughout. Such a
$B$ contains $M_0$, and can be strictly larger than the Iwahori subgroups of Moy and Prasad (the
minimal parahoric subgroups, which are subgroups of finite index of the stabilizers of points of the
building and equal them when $\mathbf{G}$ is semisimple and simply connected).

1. For every admissible representation $(\pi, V)$ of $G$, the canonical projection from $V^B$ to
   the $M_0$-invariants $(V_N)^{M_0}$ of the Jacquet module $V_N = V/V(N)$ is a linear
   isomorphism.
2. An irreducible admissible representation $(\pi, V)$ of $G$ with $V^B \ne 0$ embeds into
   $I(\chi)$ for some unramified character $\chi$ of $M$. Conversely, every nonzero $G$-stable
   subspace $V$ of an unramified principal series $I(\chi)$ satisfies $V^B \ne 0$.

Since $V^{gBg^{-1}} = \pi(g)V^B$, item 2 also holds with $B$ replaced by any $G$-conjugate of $B$.

## Depends on

- [Smooth and admissible representations of p-adic groups](smooth-representations-of-p-adic-groups.md)
- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md), for normalized parabolic induction and Jacquet modules
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for minimal parabolic subgroups, the building, its apartments, chambers and special points, and the Iwahori subgroup fixing a chamber in Casselman's convention, with its Iwahori factorization

## Proof depends on

- [Parabolic induction and Jacquet functors](parabolic-induction-and-jacquet-functors.md), for Frobenius reciprocity and for Jacquet's surjectivity theorem (item 6 there: for a compact open subgroup with an Iwahori factorization, here $B = N_1^- M_0 N_0$, the projection $V^{B} \to (V_N)^{M_0}$ is surjective)
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the Iwahori factorization of $B$ and the decomposition of $G$ into the double cosets $PwB$
- [Jacquet modules and the asymptotics of matrix coefficients](asymptotics-of-matrix-coefficients.md), for the vanishing of $\pi(\mathrm{ch}_{BaB})v$ on $V(N)$ for $a$ deep in $A^-$, used for injectivity

## Sources

- W. Casselman, "The unramified principal series of p-adic groups I. The spherical function",
  Compositio Math. 40 (1980), 387–406, <http://www.numdam.org/item?id=CM_1980__40_3_387_0>:
  introduction (setting: $k$ a non-archimedean locally compact field, $\mathbf{G}$ connected
  reductive), §1 (the building, the special point $x_0$ and the Iwahori subgroup $B$ fixing the
  chamber $C$, and (23), its Iwahori factorization $B = N_1^- M_0 N_0$), §2 (unramified characters and the unramified
  principal series $I(\chi)$), Proposition 2.4 (item 1; "This proof of injectivity is Borel's (see
  Lemma 4.7 of [1])", A. Borel, Invent. Math. 35 (1976)) and Proposition 2.6 (item 2).
- A. Moy and G. Prasad, "Jacquet functors and unrefined minimal K-types", Comment. Math. Helv. 71
  (1996), 98–121, <https://doi.org/10.5169/seals-53837>: §1 (Borel's results stated for
  subquotients of unramified principal series), §3.1 (parahoric subgroups, "a certain subgroup of
  finite index in the isotropy group", which coincides with it for semisimple simply connected
  groups; Iwahori subgroups as minimal parahoric subgroups) and Theorem 2.2 (Jacquet's surjectivity
  for compact open subgroups with an Iwahori decomposition).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a form of this theorem as `GlobalTheory.Published.BorelCasselman`.
