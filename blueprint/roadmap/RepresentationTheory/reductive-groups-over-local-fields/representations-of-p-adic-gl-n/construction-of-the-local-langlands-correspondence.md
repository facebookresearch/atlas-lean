# Construction of the local Langlands correspondence for GLₙ

This node is still to be broken down. It covers the proofs of existence of the
[local Langlands correspondence for GLₙ](local-langlands-correspondence-for-gl-n.md) over a finite
extension $F$ of $\mathbb{Q}_p$, and the reductions by which it suffices to construct a family of
maps $\mathrm{rec}_n$ from the supercuspidal representations of $\mathrm{GL}_n(F)$ to the
irreducible $n$-dimensional representations of $W_F$ that satisfies the five properties of the
correspondence (compatibility with local class field theory for $n = 1$, with $L$- and
$\varepsilon$-factors of pairs, with twists, central characters and contragredients) on
supercuspidal representations.

- **Reductions** (mostly due to Henniart; Wedhorn (4.2.2)–(4.2.5)), for such a family: its
  extension to all irreducible representations by
  $\mathrm{rec}(L(\Delta_1, \dots, \Delta_r)) = \bigoplus_i \mathrm{rec}(\pi_i) \otimes \mathrm{Sp}(m_i)$
  for $\Delta_i = [\pi_i, \nu^{m_i - 1}\pi_i]$, through the Langlands classification and the
  decomposition of Weil–Deligne representations into indecomposables, the extension satisfying the
  five properties by the inductive description of the factors of pairs; injectivity on
  supercuspidal representations from the poles at $s = 0$ of the $L$-factors of pairs; and
  surjectivity from the preservation of conductors, which follows from that of $\varepsilon$-factors
  of pairs, and Henniart's numerical local Langlands correspondence, by which the supercuspidal
  representations and the irreducible representations of $W_F$ with a given conductor and central
  character form finite sets of the same size.
- **Harris–Taylor.** The realization of the correspondence in the cohomology of the vanishing
  cycles on the deformation spaces of special formal $p$-divisible $\mathcal{O}_F$-modules
  (Lubin–Tate spaces), through the cohomology of simple Shimura varieties of PEL type and the
  Jacquet–Langlands correspondence.
- **Henniart.** A simpler proof.
- **Scholze.** A new proof for supercuspidal representations, characterizing the correspondence by
  the traces of test functions $f_{\tau,h}$ built from the vanishing cycles on deformation spaces
  of $p$-divisible groups, through the cohomology of Shimura varieties of unitary groups of
  signature $(1, n-1)$, following Kottwitz.

## Expansion

A good expansion has pages for the reductions, each stated for a family of maps on supercuspidal
representations with the five properties and citing Wedhorn's (4.2.2)–(4.2.5) and Henniart's
papers with locators, a page for Henniart's numerical local Langlands correspondence, and further
nodes for the geometric and global inputs of the proofs (Lubin–Tate spaces and their vanishing
cycles, the Jacquet–Langlands correspondence, the Shimura varieties used), placed in their own
fields.

## Depends on

- [Cuspidal representations and Jacquet's embedding theorem](../representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for supercuspidal representations
- [Smooth and admissible representations of p-adic groups](../representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for twists, central characters and contragredients
- [L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](l-and-epsilon-factors-of-pairs.md), for the factors of pairs on both sides and the Weil–Deligne representations $\mathrm{Sp}(m)$; that page uses the Weil group $W_F$ without defining it
- [Langlands classification for GLₙ](langlands-classification-for-gl-n.md), for the representations $L(\Delta_1, \dots, \Delta_r)$ of the reductions
- [Local class field theory: the local Artin map](../../../NumberTheory/p-adic-numbers/local-class-field-theory.md), for the compatibility with local class field theory for $n = 1$
- [Weil–Deligne representations](../../../NumberTheory/algebraic-number-theory/galois-representations/weil-deligne-representations/weil-deligne-representations.md), for the Weil–Deligne representations and their monodromy
- [Weil group of a p-adic field](../../../NumberTheory/algebraic-number-theory/galois-representations/weil-deligne-representations/weil-group-of-a-p-adic-field.md), for the Weil group $W_F$ of the finite extension $F$ of $\mathbb{Q}_p$ (Wedhorn, §1.1), for the Galois side; its representations are the Weil–Deligne representations with $N = 0$

## Proof depends on

- [Langlands classification for GLₙ](langlands-classification-for-gl-n.md), for the extension from supercuspidal to all irreducible representations through the representations $L(\Delta_1, \dots, \Delta_r)$
- [L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](l-and-epsilon-factors-of-pairs.md), for the Weil–Deligne representations $\mathrm{Sp}(m)$, the decomposition into indecomposables $\rho_0 \otimes \mathrm{Sp}(m)$, the inductive description of the factors of pairs on both sides, the poles of the $L$-factors of pairs of supercuspidal representations and the conductors
- [Cuspidal representations and Jacquet's embedding theorem](../representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for supercuspidal representations
- [Local converse theorem for GLₙ](local-converse-theorem-for-gl-n.md), for the uniqueness of such a family of maps, Wedhorn's reduction (4.2.3), through Henniart's theorem that supercuspidal representations are determined by their $\varepsilon$-factors of pairs

## Sources

- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): the introduction (the history and an outline of the construction
  of Harris and Taylor), §4.2, (4.2.1)–(4.2.5) (the reductions), §4.4 (the construction after
  Harris and Taylor) and §5 (Jacquet–Langlands theory, special $p$-divisible $\mathcal{O}$-modules,
  deformations and vanishing cycles).
- M. Harris and R. Taylor, *The geometry and cohomology of some simple Shimura varieties*, cited by
  Wedhorn ([HT]) as a 1999 Harvard preprint.
- G. Henniart, "Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique",
  Invent. Math. 139 (2000), 439–455, and "La conjecture de Langlands numérique pour GL(n)", Ann.
  Sci. École Norm. Sup. (4) 21 (1988), 497–544, as cited by Wedhorn ([He4], [He2]).
- P. Scholze, "The local Langlands correspondence for GL_n over p-adic fields", Invent. Math. 192
  (2013), arXiv:1010.1540 (version 1): §1, Theorems 1.1–1.4.
- G. Laumon, M. Rapoport and U. Stuhler, "D-elliptic sheaves and the Langlands correspondence",
  Invent. Math. 113 (1993), 217–338, the case of local fields of positive characteristic, as cited
  by Wedhorn ([LRS]).
