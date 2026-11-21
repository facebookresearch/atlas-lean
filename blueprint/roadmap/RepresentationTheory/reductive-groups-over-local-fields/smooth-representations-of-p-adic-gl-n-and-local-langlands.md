# Smooth representations of p-adic GLₙ and the local Langlands correspondence

This node covers smooth representations, on complex vector spaces, of reductive groups over a
non-archimedean local field $F$, chiefly of $G_n = \mathrm{GL}_n(F)$, and the local Langlands
correspondence for the groups $G_n$. Write $\nu = \lvert \det \rvert_F$.

- **Induction and Jacquet modules.** For a reductive $p$-adic group $G$ and a Levi subgroup $M$
  of a parabolic subgroup, normalized parabolic induction $i_{G,M}$ and the Jacquet functor
  $r_{M,G}$ are exact, $r_{M,G}$ is left adjoint to $i_{G,M}$, and both carry admissible
  representations to admissible ones (the Jacquet functor by a theorem of Jacquet).
- **Cuspidal support.** Every irreducible smooth representation of $G$ embeds in
  $i_{G,M}(\rho)$ for some Levi subgroup $M$ and some irreducible cuspidal representation $\rho$ of
  $M$; in particular it is admissible (Jacquet).
- **Depth.** Moy and Prasad attach to each point $x$ of the Bruhat–Tits building of $G$ a
  filtration $(G_{x,r})_{r \ge 0}$ of the parahoric subgroup $G_x = G_{x,0}$. Every irreducible
  admissible representation $\pi$ of $G$ has a depth $\rho(\pi) \in \mathbb{Q}_{\ge 0}$: for some
  $x$ the vectors fixed by $G_{x,\rho(\pi)+}$ are nonzero, and $\rho(\pi)$ is the least number with
  this property. Moreover $\pi$ contains an unrefined minimal $K$-type of depth $\rho(\pi)$, and any
  two unrefined minimal $K$-types contained in $\pi$ are associate. An unrefined minimal $K$-type of
  depth zero is the inflation to a parahoric subgroup $G_x$ of a cuspidal representation of the
  finite reductive quotient $G_x/G_{x,0+}$.
- **Geometric lemma.** For standard Levi subgroups $M$ and $N$, relative to the chosen minimal
  parabolic subgroup, the functor $r_{N,G} \circ i_{G,M}$ has a filtration, functorial in the
  representation, whose subquotients are the functors $i_{N, N'} \circ w \circ r_{M', M}$ for $w$ in
  the set $W^{M,N}$ of distinguished representatives of the double cosets $W_N \backslash W / W_M$,
  where $M' = M \cap w^{-1}(N)$ and $N' = w(M) \cap N$ (Bernstein–Zelevinsky, §§2.11–2.12).
- **Finite length.** A representation induced from an irreducible cuspidal representation has
  finite length; with the embedding theorem and the geometric lemma it follows that parabolic
  induction and Jacquet functors carry representations of finite length to representations of
  finite length.
- **Zelevinsky's classification.** Write $\times$ for the product of representations of the $G_n$
  given by parabolic induction. A segment is a set
  $\Delta = \{\rho, \nu\rho, \dots, \nu^{k}\rho\}$, $k \ge 0$, with $\rho$ an irreducible
  cuspidal representation of some $G_m$; two segments are linked if neither contains the other and
  their union is a segment. The representation $\rho \times \nu\rho \times \dots \times \nu^k\rho$
  has a unique irreducible subrepresentation $\langle \Delta \rangle$, and
  $\nu^k\rho \times \dots \times \nu\rho \times \rho$ has a unique irreducible subrepresentation
  $\langle \Delta \rangle^t$. The map $a \mapsto \langle a \rangle$ is a bijection from finite
  multisets of segments onto the irreducible representations of all the $G_n$; the Grothendieck
  ring $\bigoplus_n R(G_n)$ is a polynomial ring over $\mathbb{Z}$ in the classes
  $\langle \Delta \rangle$; and $\langle \Delta_1 \rangle \times \dots \times \langle \Delta_r \rangle$
  is irreducible if and only if no two of the segments are linked, and the same holds for
  $\langle \Delta_1 \rangle^t \times \dots \times \langle \Delta_r \rangle^t$. An irreducible representation is
  essentially square-integrable if and only if it is isomorphic to $\langle \Delta \rangle^t$ for a
  segment $\Delta$ (Bernstein). The Langlands classification gives a second parametrization of the
  irreducible representations by multisets of segments.
- **Tempered and unitary representations.** The product of two irreducible unitary
  representations is irreducible and unitary (Bernstein). For $F$ of characteristic zero, an
  irreducible representation of $G_n$ is tempered if and only if it is a product
  $\langle \Delta_1 \rangle^t \times \dots \times \langle \Delta_r \rangle^t$ of square-integrable
  representations, and Tadić classifies the irreducible unitary representations of all the
  $G_n$.
- **Iwahori-fixed vectors.** Let $G$ be the group of $F$-points of a connected reductive group
  over $F$ and $B$ an Iwahori subgroup. An irreducible admissible representation of $G$ with
  nonzero $B$-fixed vectors embeds in an unramified principal series, and every nonzero $G$-stable
  subspace of an unramified principal series has nonzero $B$-fixed vectors (Borel, Casselman).
- **Whittaker models.** For every irreducible representation $\omega$ of $G_n$ there is a
  character $\theta$ of the group $U$ of upper triangular unipotent matrices, built from the
  derivatives of $\omega$, such that $\omega$ embeds in the representation of $G_n$ induced from
  $\theta$, the embedding being unique up to a scalar (Zelevinsky's degenerate Whittaker model; for
  generic $\omega$ this is the uniqueness, up to a scalar, of Whittaker functionals, due to Gelfand
  and Kazhdan). The contragredient of an irreducible smooth representation $\pi$ is isomorphic to
  $g \mapsto \pi({}^t g^{-1})$ (Gelfand–Kazhdan).
- **Local Langlands correspondence.** For $F$ a finite extension of $\mathbb{Q}_p$ there is a unique
  family of bijections $\mathrm{rec}_n$ from the irreducible admissible representations of $G_n$
  to the $n$-dimensional Frobenius-semisimple Weil–Deligne representations of the Weil group $W_F$
  such that $\mathrm{rec}_1$ is given by local class field theory, $\mathrm{rec}_n$ preserves
  $L$- and $\varepsilon$-factors of pairs, and $\mathrm{rec}_n$ is compatible with twists by
  characters, central characters and contragredients (existence: Harris–Taylor, Henniart;
  uniqueness: Henniart, who first showed that a correspondence between irreducible representations
  of $W_F$ and supercuspidal representations is determined by local class field theory and
  $\varepsilon$-factors of pairs, and then that the whole family is characterized by local class
  field theory and $L$- and $\varepsilon$-factors of pairs). Supercuspidal representations correspond
  to irreducible representations and essentially square-integrable ones to indecomposable ones. For
  local fields of positive characteristic the correspondence is due to Laumon, Rapoport and
  Stuhler.
- **Local converse theorem.** Two irreducible generic representations of $G_n$ with the same
  central character whose twisted $\gamma$-factors $\gamma(s, \pi_i \times \tau, \psi)$ agree for
  all irreducible generic representations $\tau$ of $G_r$, $1 \le r \le \lfloor n/2 \rfloor$, are
  isomorphic (Jacquet–Liu, Chai). For $n \ge 2$, Henniart had proved that twists by the irreducible
  generic representations of $G_{n-1}$ suffice; for $n = 1$ the central character determines the
  representation.

Representations of real groups and the Weil representation are outside this node.

## Expansion

A good expansion replaces this node by definition pages and statements in the following order,
each citing the source and locator below.

1. Smooth and admissible representations, contragredients, normalized parabolic induction and the
   Jacquet functor, with exactness, adjunction and preservation of admissibility.
2. Cuspidal representations, the embedding theorem and admissibility of irreducible representations,
   the geometric lemma, which uses step 1, and then the finite length of representations induced
   from cuspidal ones and the preservation of finite length, which use them; Moy–Prasad filtrations
   and depth.
3. For $G_n$: the product of representations, segments and linking, the representations
   $\langle \Delta \rangle$, Zelevinsky's classification, the polynomial structure of the
   Grothendieck ring, the irreducibility criterion, essentially square-integrable representations,
   and the Langlands classification, which use step 2.
4. Tempered representations, Bernstein's irreducibility theorem and Tadić's classification of the
   unitary dual.
5. Iwahori subgroups and the Borel–Casselman theorem.
6. Whittaker models, uniqueness, and the Gelfand–Kazhdan theorem.
7. Weil–Deligne representations and their $L$- and $\varepsilon$-factors (the Galois side is
   described under [Galois representations and p-adic Hodge theory](../../NumberTheory/galois-representations/README.md)),
   $L$- and $\varepsilon$-factors of pairs of representations of $G_n \times G_m$, the local converse
   theorems, and the local Langlands correspondence with its characterization.

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §§1.2–1.8 (smooth and admissible
  representations, the functors $i$ and $r$), Proposition 2.3 (exactness, adjunction,
  admissibility), §2.4 and Theorem 2.5 (cuspidal representations and the embedding theorem, with
  references to Jacquet and, for $\mathrm{GL}_n$, to Bernstein–Zelevinsky 1976), Theorem 2.8 (finite
  length of representations induced from cuspidal ones), Lemma 2.11 and the Geometrical Lemma 2.12.
- A. V. Zelevinsky, "Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)", Ann. Sci. École Norm. Sup. (4) 13 (1980), 165–210,
  <http://www.numdam.org/item?id=ASENS_1980_4_13_2_165_0>: Proposition 1.4 (finite length, proved
  from Bernstein–Zelevinsky 1977, 2.5, 2.8 and 2.12),
  Theorem 4.2 (irreducibility criterion), Theorems 6.1 and 6.5 (classification), Corollary 7.5
  (Grothendieck ring), the Corollary in §8.3 (degenerate Whittaker models, realized "in a unique
  way") with the reference there to Gelfand–Kazhdan, Theorem 9.3 (essentially
  square-integrable representations, due to Bernstein) and Theorem 9.7.
- W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, notes, draft of 1 May 1995, <https://personal.math.ubc.ca/~cass/research/pdf/p-adic-book.pdf>:
  Theorem 3.3.1 (Jacquet modules), Theorem 5.1.2 (embedding theorem, due to Jacquet), the
  Corollary of the Corollary 6.3.8 (finite length of induced representations) and Theorem 6.3.10
  (finitely generated admissible representations have finite length).
- M. Tadić, "Classification of unitary representations in irreducible representations of general
  linear group (non-Archimedean case)", Ann. Sci. École Norm. Sup. (4) 19 (1986), 335–382,
  <http://www.numdam.org/item?id=ASENS_1986_4_19_3_335_0>: Theorem 2.5 (Bernstein's irreducibility
  theorem, from I. N. Bernstein, LNM 1041 (1984), 50–102), Theorems A and D (unitary dual; the
  Appendix proves the results of §§7–8 in characteristic zero without a result then only announced),
  §§5.1–5.4 (Langlands classification, following Rodier).
- W. Casselman, "The unramified principal series of p-adic groups I. The spherical function",
  Compositio Math. 40 (1980), 387–406, <http://www.numdam.org/item?id=CM_1980__40_3_387_0>:
  Propositions 2.4 and 2.6 (Iwahori-fixed vectors; the injectivity argument is credited there to
  A. Borel, Invent. Math. 35 (1976), Lemma 4.7).
- A. Moy and G. Prasad, "Jacquet functors and unrefined minimal K-types", Comment. Math. Helv. 71
  (1996), 98–121, <https://doi.org/10.5169/seals-53837>: §1, §3.1 (parahoric subgroups and their
  filtrations for a reductive group), §3.4 (unrefined minimal K-types and associativity) and
  Theorem 3.5 (depth). This extends Theorem 5.2 of A. Moy and G. Prasad, "Unrefined minimal K-types
  for p-adic groups", Invent. Math. 116 (1994), 393–408, which treats absolutely quasi-simple, simply
  connected groups over fields of characteristic zero.
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): Theorem (1.2.2) (the correspondence and its characterizing
  properties), Theorem (1.2.3) (supercuspidal and essentially square-integrable representations),
  (2.1.22) (Gelfand–Kazhdan), (2.2.9) (Langlands classification), (2.3.7)–(2.3.8) (tempered
  representations), (4.2.2)–(4.2.3) (reduction to supercuspidal representations; uniqueness through
  Henniart's theorem), and the introduction (Harris–Taylor, Henniart; Laumon–Rapoport–Stuhler for
  local fields of positive characteristic).
- G. Henniart, "Caractérisation de la correspondance de Langlands locale par les facteurs ε de
  paires", Invent. Math. 113 (1993), 339–350,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0113>: the summary (a correspondence between
  irreducible representations of the Weil group and supercuspidal representations is determined by
  local class field theory and $\varepsilon$-factors of pairs), Théorème 1.1 (generic representations
  of $\mathrm{GL}_n$, $\gamma$-factors twisted by the generic representations of $\mathrm{GL}_{n-1}$)
  and its Corollaire (supercuspidal representations, $\varepsilon$-factors twisted by the supercuspidal
  representations of $\mathrm{GL}_r$ for $1 \le r \le n - 1$).
- G. Henniart, "Une caractérisation de la correspondance de Langlands locale pour GL(n)", Bull. Soc.
  Math. France 130 (2002), 587–602, <http://www.numdam.org/item/BSMF_2002__130_4_587_0/>: §1.8,
  Corollaire (the family of correspondences for all $n$ is characterized by local class field theory
  and $L$- and $\varepsilon$-factors of pairs).
- P. Scholze, "The local Langlands correspondence for GL_n over p-adic fields", Invent. Math. 192
  (2013), arXiv:1010.1540 (version 1): Theorem 1.2 (a new proof for supercuspidal representations
  and irreducible representations of the Weil group).
- H. Jacquet and B. Liu, "On the local converse theorem for p-adic GL_n", Amer. J. Math. 140
  (2018), arXiv:1601.03656 (version 3): Conjecture 1.1 and Theorem 1.3; J. Chai, "Bessel functions
  and local converse conjecture of Jacquet", arXiv:1601.05450 (version 2): Theorem 1.1.
- Proof of the Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet
  L-functions: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>).
  Statement and proof of the Riemann hypothesis certified by the Lean and Mathlib communities in a
  joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative
  (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); independent checks of
  its five main theorems by A. Sutherland (<https://math.mit.edu/~drew/grh/>). Source mirror:
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
  The library has no licence, so none of its Lean comes into ATLAS; ATLAS has no Lean proof of
  its own. Related formal statements in Alpöge's proof, often in specialised forms,
  include `GlobalTheory.Published.IrreducibleAdmissibleGL`,
  `GlobalTheory.Published.BernsteinZelevinskyFiniteness`, `GlobalTheory.Published.GeometricLemma`,
  `GlobalTheory.Published.SegmentRepresentation`, `GlobalTheory.Published.LanglandsMultisegments`,
  `GlobalTheory.Published.BorelCasselman`, `GlobalTheory.Published.LocalConverseGL` (for cuspidal
  representations of $\mathrm{GL}_{m+1}$, with $\varepsilon$-factors twisted by $\mathrm{GL}_m$) and
  `UpperTheory.Zero.LLC.recTExists` (at the completions of number fields, a map from irreducible
  representations of the groups $\mathrm{GL}_n$ to Weil–Deligne representations satisfying a
  restricted list of laws, not the full correspondence stated above).
