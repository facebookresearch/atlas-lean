# Zelevinsky's classification of the irreducible representations of GLₙ

Let $F$ be a non-archimedean local field, $G_n = \mathrm{GL}_n(F)$ ($G_0$ the trivial group) and
$\nu = \lvert \det \rvert_F$. For smooth representations $\pi_1$ of $G_{n_1}$ and $\pi_2$ of
$G_{n_2}$, the **product** $\pi_1 \times \pi_2$ is the representation of $G_{n_1+n_2}$
parabolically induced, by [normalized induction](../representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md),
from $\pi_1 \otimes \pi_2$ on the block-diagonal Levi subgroup $G_{n_1} \times G_{n_2}$. Let $R_n$
be the Grothendieck group of smooth representations of $G_n$ of finite length and
$R = \bigoplus_{n \ge 0} R_n$; the product makes $R$ a commutative graded ring. Let $\mathcal{C}$ be
the set of isomorphism classes of irreducible
[cuspidal](../representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md) representations of the groups $G_m$,
$m \ge 1$.

- A **segment** is a set $\Delta = [\rho, \nu^k\rho] = \{\rho, \nu\rho, \dots, \nu^k\rho\}$ with
  $\rho \in \mathcal{C}$ and an integer $k \ge 0$. Two segments $\Delta_1$, $\Delta_2$ are
  **linked** if $\Delta_1 \not\subseteq \Delta_2$, $\Delta_2 \not\subseteq \Delta_1$ and
  $\Delta_1 \cup \Delta_2$ is a segment; $\Delta_1 = [\rho_1, \rho_1']$ **precedes**
  $\Delta_2 = [\rho_2, \rho_2']$ if they are linked and $\rho_2 = \nu^k\rho_1$ with $k > 0$.
- For a segment $\Delta = [\rho, \nu^k\rho]$, the representation
  $\rho \times \nu\rho \times \dots \times \nu^k\rho$ has a unique irreducible subrepresentation
  $\langle \Delta \rangle$, and $\nu^k\rho \times \dots \times \nu\rho \times \rho$ has a unique
  irreducible subrepresentation $\langle \Delta \rangle^t$, which is also the unique irreducible
  quotient of $\rho \times \nu\rho \times \dots \times \nu^k\rho$.

**Theorem (Zelevinsky).**

1. Let $\Delta_1, \dots, \Delta_r$ be segments such that $\Delta_i$ does not precede $\Delta_j$
   whenever $i < j$ (every finite multiset of segments has such an ordering). Then
   $\langle \Delta_1 \rangle \times \dots \times \langle \Delta_r \rangle$ has a unique irreducible
   subrepresentation $\langle \Delta_1, \dots, \Delta_r \rangle$; it depends only on the multiset
   $a = \{\Delta_1, \dots, \Delta_r\}$ and is denoted $\langle a \rangle$ ($\langle \emptyset \rangle$
   is the trivial representation of $G_0$). The map $a \mapsto \langle a \rangle$ is a bijection
   from the finite multisets of segments onto the isomorphism classes of irreducible smooth
   representations of all the $G_n$, $n \ge 0$.
2. The ring $R$ is the polynomial ring over $\mathbb{Z}$ in the classes $\langle \Delta \rangle$,
   $\Delta$ running over the segments.
3. For segments $\Delta_1, \dots, \Delta_r$, the representation
   $\langle \Delta_1 \rangle \times \dots \times \langle \Delta_r \rangle$ is irreducible if and
   only if no two of the $\Delta_i$ are linked, and the same holds for
   $\langle \Delta_1 \rangle^t \times \dots \times \langle \Delta_r \rangle^t$.

## Depends on

- [Parabolic induction and Jacquet functors](../representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md), for normalized parabolic induction
- [Cuspidal representations and Jacquet's embedding theorem](../representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for cuspidal representations
- [Finite length of parabolically induced representations](../representations-of-p-adic-reductive-groups/finite-length-of-induced-representations.md), for the finite length of products, which makes $R$ a ring

## Proof depends on

- [The Bernstein–Zelevinsky geometric lemma](../representations-of-p-adic-reductive-groups/bernstein-zelevinsky-geometric-lemma.md)
- [Finite length of parabolically induced representations](../representations-of-p-adic-reductive-groups/finite-length-of-induced-representations.md)
- [Cuspidal representations and Jacquet's embedding theorem](../representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for the embedding of irreducible representations into products of cuspidal ones
- [Mirabolic restriction and Bernstein–Zelevinsky derivatives](bernstein-zelevinsky-derivatives.md), for the derivatives and their Leibniz rule

## Sources

- A. V. Zelevinsky, "Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)", Ann. Sci. École Norm. Sup. (4) 13 (1980), 165–210,
  <http://www.numdam.org/item?id=ASENS_1980_4_13_2_165_0>: §1.7 (the product and the ring $R$),
  Theorem 1.9 (commutativity), §3.1 (segments and $\langle \Delta \rangle$, "the unique irreducible
  submodule of $\rho \times \nu\rho \times \dots \times \rho'$", with Proposition 2.10), §4.1
  (linked and preceding segments), Theorem 4.2, Theorem 6.1 and Theorem 6.5 (item 1), Corollary
  7.5 (item 2), §9.1 ($\langle \Delta \rangle^t$) and Theorem 9.7 (a) (the irreducibility criterion
  for products of the $\langle \Delta_i \rangle^t$). The proofs use derivatives (§§3–8, after
  Bernstein–Zelevinsky 1977, §§3–4).
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): (2.2.8)–(2.2.11) (the same classification with
  $Z(\Delta) = \langle \Delta \rangle$ and $Q(\Delta) = \langle \Delta \rangle^t$, and the ring
  $R(K)$).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states forms of these results as `GlobalTheory.Published.SegmentRepresentation` and
  `GlobalTheory.Published.ZelevinskyPolynomialRing`.
