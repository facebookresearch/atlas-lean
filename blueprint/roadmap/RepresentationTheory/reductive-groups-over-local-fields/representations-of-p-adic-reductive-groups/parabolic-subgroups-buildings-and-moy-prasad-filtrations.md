# Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations

This node is still to be broken down. It covers the structure theory of a connected reductive
group $\mathbf{G}$ over a non-archimedean local field $F$ that the representation theory of
$G = \mathbf{G}(F)$ uses.

- **Parabolic subgroups.** Parabolic $F$-subgroups and their Levi decompositions $P = MU$, a
  minimal parabolic subgroup $P_0$ with a maximal split torus $A_0 \subset P_0$, the standard
  parabolic subgroups (those containing $P_0$) and the standard Levi subgroups (for a standard
  parabolic subgroup $P$, the unique Levi subgroup of $P$ containing $A_0$; a Levi subgroup of some
  parabolic subgroup that contains $A_0$ need not be standard, as the block-diagonal subgroup of
  $\mathrm{GL}_3$ for the blocks $\{1, 3\}$ and $\{2\}$ shows), the relative Weyl group
  $W = N_G(A_0)/Z_G(A_0)$ and the Weyl groups $W_M$ of standard Levi subgroups, modulus characters,
  the compactness of $G/P$, the decomposition $G = P_0 K$ for a good maximal compact subgroup $K$,
  and the compact open subgroups with an Iwahori factorization $K_0 = (K_0 \cap \bar U)(K_0 \cap M)
  (K_0 \cap U)$ with respect to $P$.
- **The Bruhat decomposition** of $G$ into double cosets of two standard parabolic subgroups,
  indexed by double cosets of Weyl groups, with the order in which the orbits can be filtered by
  open unions, and the $\ell$-sheaves on $\ell$-spaces with which Bernstein and Zelevinsky filter
  induced representations along it; and Bernstein and Zelevinsky's lemma that associate standard
  Levi subgroups $M$ and $N = w(M)$ are linked by chains of elementary maps, an elementary map
  $M' \to N'$ being given by an element of the Weyl group $W_L$ of a standard Levi subgroup $L$
  containing $M'$ and $N'$ such that $\lvert W_L(M', *)/W_{M'} \rvert = 2$, where
  $W_L(M', *) = \{ v \in W_L \mid v(M') \text{ is a standard Levi subgroup} \}$.
- **Buildings.** The enlarged Bruhat–Tits building $\mathcal{B}(\mathbf{G}, F)$, the product of
  the reduced building and the real vector space attached to the centre, its apartments and affine
  roots, chambers and special points.
- **Parahoric subgroups.** The parahoric subgroup $G_x$ attached to a point $x$ of the building,
  a subgroup of finite index of its stabilizer, equal to it when $\mathbf{G}$ is semisimple and
  simply connected; the Iwahori subgroups, which are the minimal parahoric subgroups and are all
  conjugate under $G$; Casselman's Iwahori subgroup $B$ fixing a chamber of the apartment of a
  maximal split torus $A$, which has the Iwahori factorization $B = N_1^- M_0 N_0$ with respect to
  a minimal parabolic subgroup $P = MN$ containing $A$ (so that $B \cap M$ is the maximal compact
  open subgroup $M_0$ of $M$) and can be larger than the minimal parahoric subgroups; the
  decomposition of $G$ into the double cosets $PwB$; the identification of $G_x/G_{x,0+}$ with
  the group $\mathsf{M}_x(\mathfrak{f})$ of rational points of the reductive quotient of the
  reduction of the integral model attached to $G_x$, over the residue field $\mathfrak{f}$.
- **Moy–Prasad filtrations.** For $x \in \mathcal{B}(\mathbf{G}, F)$ and real $r \ge 0$ the
  filtration subgroups $G_{x,r}$ of $G_x = G_{x,0}$, with $G_{x,r+} = \bigcup_{s > r} G_{x,s}$,
  their normality in $G_x$, the inclusions $[G_{x,r}, G_{x,s}] \subseteq G_{x,r+s}$, the lattices
  $\mathfrak{g}_{x,r}$ of the Lie algebra $\mathfrak{g}$ and $\mathfrak{g}^*_{x,r}$ of its dual
  $\mathfrak{g}^* = \mathrm{Hom}_F(\mathfrak{g}, F)$, the isomorphisms
  $G_{x,r}/G_{x,r+} \cong \mathfrak{g}_{x,r}/\mathfrak{g}_{x,r+}$ for $r > 0$, the identification of
  the Pontryagin dual of $G_{x,r}/G_{x,r+}$ with
  $\mathfrak{g}^*_{x,-r}/\mathfrak{g}^*_{x,(-r)+}$, the discreteness of the jumps of the
  filtrations, and nilpotent elements of $\mathfrak{g}^*$ (those $X$ with
  $\lim_{t \to 0} \lambda(t)X = 0$ for some one-parameter subgroup $\lambda$ over $F$).
- **Products and $\mathrm{GL}_m$.** The building, parahoric subgroups and filtrations of a product
  of groups are the products of those of the factors. The filtration subgroups $G_{x,r}$ depend
  only on the image of $x$ in the reduced building, since the affine roots are constant along the
  central direction and the central part of the filtration does not depend on $x$. For
  $\mathrm{GL}_m(F)$, the vertices of the reduced building correspond to the homothety classes of
  $\mathcal{O}_F$-lattices in $F^m$ and are all conjugate (for $\mathrm{GL}_1$ the reduced building
  is a point and the enlarged one a line); at every point $x$ over the vertex of
  $\mathcal{O}_F^m$ the parahoric subgroup is $\mathrm{GL}_m(\mathcal{O}_F)$ and $G_{x,0+}$ is the
  principal congruence subgroup $\ker(\mathrm{GL}_m(\mathcal{O}_F) \to \mathrm{GL}_m(\mathfrak{f}))$,
  and every $G_{y,0+}$ contains a conjugate of it.

## Expansion

A good expansion has definition pages for parabolic subgroups and their Levi decompositions, for
standard parabolic and Levi subgroups with their Weyl groups, for the Bruhat–Tits building, for
parahoric and Iwahori subgroups and for the Moy–Prasad filtrations of groups and lattices, and
statement pages for the Bruhat decomposition, the existence of compact open subgroups with an
Iwahori factorization (including Casselman's Iwahori subgroups and the Moy–Prasad subgroups
$G_{x,r}$, $r > 0$), the chains of elementary maps, the conjugacy of Iwahori subgroups, the case of
products and of $\mathrm{GL}_m$, and the properties of the filtrations
listed above, each citing the sources below with locators.

It also writes out these steps of its own proof:

- Bruhat–Tits theory, on which Moy and Prasad construct the filtrations: the affine building (Bruhat–Tits I, §§2 and 7), the smooth integral models (II, 4.6.2) and the fixers of bounded subsets of an apartment (II, 4.6.26–4.6.28); Moy–Prasad, §3.2, cite II, Proposition 4.6.28 (iii), for the transitivity on the apartments containing $x$, which makes $G_{x,r}$ independent of the apartment.

## Depends on

- [Linear algebraic groups over local fields and their groups of rational points](../linear-algebraic-groups-over-local-fields.md), for connected reductive groups over $F$, their maximal split tori and the topology of $G = \mathbf{G}(F)$
- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for parabolic $F$-subgroups, Levi decompositions, standard parabolic and Levi subgroups and Weyl groups
- [Relative roots, root space decompositions and root subgroups of reductive groups](../../../GroupTheory/linear-groups/relative-root-systems-and-root-subgroups.md), for relative roots and the root space decomposition of the Lie algebra, for the affine roots and the lattices $\mathfrak{g}_{x,r}$
- [ℓ-spaces, distributions and smooth representations of ℓ-groups](l-spaces-distributions-and-smooth-representations-of-l-groups.md), for $\ell$-spaces and $\ell$-sheaves (Bernstein–Zelevinsky 1976, Chapter I, §1; Bernstein–Zelevinsky 1977, §5), for the filtration of induced representations along the Bruhat decomposition

## Proof depends on

- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for the Bruhat decomposition of $G$ into double cosets of standard parabolic subgroups (Borel–Tits, 5.15 and 5.20, as cited by Bernstein–Zelevinsky 1977, §6.4)

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §2.1 (minimal parabolic subgroups,
  standard Levi subgroups and parabolic triples), §2.6 (Weyl groups), Lemma 2.17 (chains of
  elementary maps, proved in §6; for $\mathrm{GL}_n$, transpositions of neighbouring blocks), §§5.1–5.15 (the orbits of a
  parabolic subgroup on $P \backslash G$ and $\ell$-sheaves, after their Uspekhi Mat. Nauk 31 (1976)
  paper, §1).
- W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, notes, draft of 1 May 1995, <https://personal.math.ubc.ca/~cass/research/pdf/p-adic-book.pdf>:
  §§1.3–1.6 (parabolic subgroups, the sets $A^-_\Theta(\epsilon)$, Iwahori factorizations, modulus
  characters).
- W. Casselman, "The unramified principal series of p-adic groups I. The spherical function",
  Compositio Math. 40 (1980), 387–406, <http://www.numdam.org/item?id=CM_1980__40_3_387_0>: §1
  (the Bruhat–Tits building, the apartment of $A$, a special point and the Iwahori subgroup fixing
  a chamber, with its Iwahori factorization).
- A. Moy and G. Prasad, "Jacquet functors and unrefined minimal K-types", Comment. Math. Helv. 71
  (1996), 98–121, <https://doi.org/10.5169/seals-53837>: §2.1 (setting: $k$ of arbitrary
  characteristic), §3.1 (buildings, parahoric subgroups, Iwahori subgroups and their conjugacy),
  §3.2 (the filtrations $G_{x,r}$ and $G_{x,r+}$, generated by the subgroups $Z_n$, $n \ge r$, of
  the centralizer of a maximal torus split over the maximal unramified extension, which do not
  depend on $x$, and the $U_\psi$ with
  $\psi(x) \ge r$; the commutator inclusions, citing [T: 1.4.2], and $\mathsf{M}_x(\mathfrak{f})$; the independence of
  the apartment, through the transitivity on the apartments containing $x$ of F. Bruhat and J. Tits, Publ. Math.
  IHÉS 60 (1984), Proposition 4.6.28(iii)), §3.3 (the
  lattices $\mathfrak{g}_{x,r}$ and $\mathfrak{g}^*_{x,r}$ and the jumps), §3.4 (nilpotent elements
  and the duality).
- F. Bruhat and J. Tits, "Groupes réductifs sur un corps local" I and II, Publ. Math. IHÉS 41 (1972)
  and 60 (1984), cited by Moy–Prasad 1996 (§3.1, [BT1], [BT2]) for buildings, parahoric subgroups
  and their filtrations.
- A. Moy and G. Prasad, "Unrefined minimal K-types for p-adic groups", Invent. Math. 116 (1994),
  393–408, the original construction for absolutely quasi-simple, simply connected groups, cited
  for it by Moy–Prasad 1996 (§1; §3.3 for [MP: §3, 3.4]; §3.4 for [MP: 3.5, 3.7, 3.8]).
