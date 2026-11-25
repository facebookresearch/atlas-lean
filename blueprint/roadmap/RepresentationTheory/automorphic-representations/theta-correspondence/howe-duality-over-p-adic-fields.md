# Howe duality for unitary dual pairs over p-adic fields

Let $F$ be a non-archimedean local field of characteristic $0$, $E/F$ a quadratic field extension, $W$ a
skew-Hermitian space of dimension $n$ and $V$ a Hermitian space of dimension $m$ over $E$, and
$\omega = \omega_{W, V, \chi, \psi}$ the
[Weil representation](weil-representation-of-unitary-dual-pairs.md) of
$\mathrm{U}(W) \times \mathrm{U}(V)$ attached to a non-trivial character $\psi$ of $F$ and splitting
characters $\chi = (\chi_V, \chi_W)$. For an irreducible
[smooth representation](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md)
$\pi$ of $\mathrm{U}(W)$, the maximal $\pi$-isotypic quotient of $\omega$ (the quotient by the
intersection of the kernels of all $\mathrm{U}(W)$-equivariant maps $\omega \to \pi$) is isomorphic to
$\pi \otimes \Theta(\pi)$ for a smooth representation $\Theta(\pi) = \Theta_{W, V, \psi}(\pi)$ of
$\mathrm{U}(V)$, unique up to isomorphism and zero if $\pi$ is not a quotient of $\omega$. Let $\theta(\pi)$
be the maximal semisimple quotient of $\Theta(\pi)$.

1. **Finite length** (Kudla's method, stated for unitary pairs by Gan and Takeda). $\Theta(\pi)$ has finite
   length.
2. **Howe duality** (Waldspurger for odd residue characteristic; Gan–Takeda in general). $\theta(\pi)$ is
   either zero or irreducible, and if $\pi'$ is another irreducible representation with
   $\theta(\pi) \cong \theta(\pi') \ne 0$, then $\pi \cong \pi'$; equivalently,
   $\dim \mathrm{Hom}_{\mathrm{U}(V)}(\theta(\pi), \theta(\pi')) \le 1$, with equality only if $\pi \cong \pi'$.
   Thus $\pi \mapsto \theta(\pi)$ is a bijection between the irreducible representations of
   $\mathrm{U}(W)$ and of $\mathrm{U}(V)$ that occur as quotients of $\omega$, the local theta
   correspondence.
3. **Supercuspidal representations** (Kudla's method, stated for unitary pairs by Gan and Takeda). If $\pi$
   is supercuspidal, then $\Theta(\pi)$ is zero or
   irreducible, and $\Theta(\pi) \cong \Theta(\pi') \ne 0$ for supercuspidal $\pi'$ implies
   $\pi \cong \pi'$.
4. **Split case** (Mínguez). For $m, n \ge 1$ and the type II dual pair $(\mathrm{GL}_n(F), \mathrm{GL}_m(F))$ in
   $\mathrm{Sp}_{2nm}(F)$, acting on $\mathcal{S}(\mathrm{M}_{n \times m}(F))$ by the normalized matrix action, which the same
   construction gives when $E = F \times F$ (the local situation of a global unitary dual pair at a place of
   $F$ that splits in $E$, with the identifications of the
   [split case](weil-representation-of-unitary-dual-pairs.md), where one factor is identified with
   $\mathrm{GL}_n(F)$ through the contragredient): if $\pi$ occurs as a quotient of the Weil representation, then $\theta(\pi)$ is
   irreducible, and $\dim \mathrm{Hom}(\omega, \pi \otimes \pi') \le 1$ for irreducible $\pi$, $\pi'$. The
   assertion that every $\pi$ occurs needs $n \le m$ and is not claimed here.

Gan and Takeda's theorem holds for non-archimedean local fields of characteristic different from $2$, and
Mínguez's in any characteristic; this page states the characteristic-$0$ case, to which the linked
construction of the Weil representation applies.

## Depends on

- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for $\omega_{W, V, \chi, \psi}$
- [Smooth and admissible representations of p-adic groups](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for irreducible smooth representations, isotypic quotients and finite length
- [Cuspidal representations and Jacquet's embedding theorem](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for supercuspidal representations in item 3

## Proof depends on

- [Jacquet modules of the Weil representation and degenerate principal series](jacquet-modules-of-the-weil-representation.md), for Kudla's filtration (with its twists by the splitting characters), the MVW involution, Bernstein's second adjointness, and, in the see-saw argument of Gan and Takeda for item 2, the twisted see-saw identity on the doubled space, the irreducibility of the lift $\Theta(\chi_W)$ of the character $\chi_W$, Rallis's embedding of it into $I(s_{m,n})$ and the surjection $I(-s_{m,n}) \twoheadrightarrow \Theta(\chi_W)$ when $s_{m,n} \le 0$; also for the rank filtration of the type II model used by Mínguez for item 4
- [Parabolic induction and Jacquet functors](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md), for the standard Frobenius reciprocity and the exactness of Jacquet functors
- [The Bernstein–Zelevinsky geometric lemma](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/bernstein-zelevinsky-geometric-lemma.md), for the Jacquet modules of induced representations used by Gan and Takeda (Lemma 5.2, proved in their appendix with Tadić's formulas)
- [Cuspidal representations and Jacquet's embedding theorem](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for the supercuspidal representations of general linear groups whose induced representations Gan and Takeda study in their Lemma 5.2
- [Zelevinsky's classification of the irreducible representations of GLₙ](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/zelevinsky-classification.md), for the irreducibility of the products $1 \times \dots \times 1$ of trivial characters used in the boundary case (Gan–Takeda §5, citing Zelevinsky's Theorem 9.7 (a))
- [Whittaker models and the Gelfand–Kazhdan theorems for GLₙ](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/whittaker-models-for-gl-n.md), for the genericity of these products (repeated singleton segments are not linked), which Gan and Takeda use through a non-zero Whittaker functional in §5

## Sources

- W. T. Gan and S. Takeda, "A proof of the Howe duality conjecture", J. Amer. Math. Soc. 29 (2016),
  473–493, arXiv:1407.1995 (version 4): §1 (the definitions of $\Theta(\pi)$ and $\theta(\pi)$, finite length
  by S. S. Kudla, Invent. Math. 83 (1986), the Howe duality conjecture and its reformulation (HD)),
  Theorem 1.1 (i) and (iii) (Kudla's theorem on supercuspidals; J.-L. Waldspurger's theorem for $p \ne 2$),
  Theorem 1.2 (the conjecture holds for symplectic–orthogonal and unitary pairs, in any residue
  characteristic), remark (2) after it (the split case, A. Mínguez, Ann. Sci. Éc. Norm. Supér. 41 (2008),
  717–741), §2.4 (the standard Frobenius reciprocity and Bernstein's Frobenius reciprocity), the acknowledgement
  of the geometric lemma, and §§2.7, 3.1, 3.2 and 4–6 (the proof: §4 the see-saw argument, with (4.1)–(4.3)
  and the surjection taken from W. T. Gan and A. Ichino, Invent. Math. 195 (2014), Proposition 8.2; §5 the
  boundary case, with Lemma 5.2 proved in the appendix; §6 the conclusion).
- A. Mínguez, "Correspondance de Howe explicite : paires duales de type II", Ann. Sci. Éc. Norm. Supér. (4)
  41 (2008), 717–741: Théorème 1 (1) (p. 718), (1.4) and Corollaire 6.3 (p. 734), for item 4, with the proof
  in §§2–6.
- S. S. Kudla, "Notes on the local theta correspondence", lecture notes, European School in Group
  Theory, 1996, <https://www.math.toronto.edu/~skudla/castle.pdf>: §II.1 (type I and type II dual pairs)
  and §II.2 (the maximal isotypic quotient and the Howe duality principle).
- M. Harris, S. S. Kudla and W. J. Sweet, "Theta dichotomy for unitary groups", J. Amer. Math. Soc. 9
  (1996), 941–1004, <https://doi.org/10.1090/S0894-0347-96-00198-1>: introduction, (0.4) (the Howe
  duality principle for unitary pairs).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states specialized results (matrix Weil data, the isotypic-kernel characterization, finite length and
  uniqueness of the irreducible quotient when it is non-zero) as `GlobalTheory.Published.HoweDualityUnitary` and, for the split case
  with positive ranks, `GlobalTheory.Published.MinguezThetaGL`.
