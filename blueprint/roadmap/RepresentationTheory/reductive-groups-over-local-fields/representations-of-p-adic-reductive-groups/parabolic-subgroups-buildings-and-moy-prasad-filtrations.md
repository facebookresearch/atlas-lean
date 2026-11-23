# Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations

This node is still to be broken down. It covers the structure theory of a connected reductive
group $\mathbf{G}$ over a non-archimedean local field $F$ that the representation theory of
$G = \mathbf{G}(F)$ uses.

- **Parabolic subgroups.** Parabolic $F$-subgroups and their Levi decompositions $P = MU$, a
  minimal parabolic subgroup $P_0$ with a maximal split torus $A_0 \subset P_0$, the standard
  parabolic and Levi subgroups (those containing $P_0$, respectively $A_0$), the relative Weyl group
  $W = N_G(A_0)/Z_G(A_0)$ and the Weyl groups $W_M$ of standard Levi subgroups, modulus characters,
  the compactness of $G/P$, the decomposition $G = P_0 K$ for a good maximal compact subgroup $K$,
  and the compact open subgroups with an Iwahori factorization $K_0 = (K_0 \cap \bar U)(K_0 \cap M)
  (K_0 \cap U)$ with respect to $P$.
- **The Bruhat decomposition** of $G$ into double cosets of two standard parabolic subgroups,
  indexed by double cosets of Weyl groups, with the order in which the orbits can be filtered by
  open unions, and the $\ell$-sheaves on $\ell$-spaces with which Bernstein and Zelevinsky filter
  induced representations along it.
- **Buildings.** The enlarged Bruhat–Tits building $\mathcal{B}(\mathbf{G}, F)$, its apartments
  and affine roots, chambers and special points.
- **Parahoric subgroups.** The parahoric subgroup $G_x$ attached to a point $x$ of the building,
  a subgroup of finite index of its stabilizer; the Iwahori subgroups, which are the minimal
  parahoric subgroups and are all conjugate under $G$; the identification of $G_x/G_{x,0+}$ with
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

A good expansion has definition pages for parabolic subgroups and their Levi decompositions, for
standard parabolic and Levi subgroups with their Weyl groups, for the Bruhat–Tits building, for
parahoric and Iwahori subgroups and for the Moy–Prasad filtrations of groups and lattices, and
statement pages for the Bruhat decomposition, the existence of compact open subgroups with an
Iwahori factorization, the conjugacy of Iwahori subgroups, and the properties of the filtrations
listed above, each citing the sources below with locators.

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §2.1 (minimal parabolic subgroups,
  standard Levi subgroups and parabolic triples), §2.6 (Weyl groups), §§5.1–5.15 (the orbits of a
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
  §3.2 (the filtrations $G_{x,r}$ and $G_{x,r+}$, the commutator inclusions and $\mathsf{M}_x(\mathfrak{f})$,
  citing F. Bruhat and J. Tits, Publ. Math. IHÉS 60 (1984), Proposition 4.6.28(iii)), §3.3 (the
  lattices $\mathfrak{g}_{x,r}$ and $\mathfrak{g}^*_{x,r}$ and the jumps), §3.4 (nilpotent elements
  and the duality).
- A. Moy and G. Prasad, "Unrefined minimal K-types for p-adic groups", Invent. Math. 116 (1994),
  393–408, the original construction for absolutely quasi-simple, simply connected groups, cited
  for it by Moy–Prasad 1996 (§1; §3.3 for [MP: §3, 3.4]; §3.4 for [MP: 3.5, 3.7, 3.8]).
