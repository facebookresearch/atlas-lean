# Local Langlands correspondence for GLₙ

Let $F$ be a finite extension of $\mathbb{Q}_p$ with Weil group $W_F$, and $\psi$ a nontrivial
additive character of $F$. For $n \ge 1$ let $\mathcal{A}_n(F)$ be the set of isomorphism classes
of irreducible admissible (equivalently, irreducible smooth) representations of $\mathrm{GL}_n(F)$
and $\mathcal{G}_n(F)$ the set of isomorphism classes of $n$-dimensional Frobenius-semisimple
complex Weil–Deligne representations of $W_F$. The local Artin map
$\mathrm{rec}_F \colon F^\times \to \mathrm{Gal}(F^{\mathrm{ab}}/F)$ of
[local class field theory](../../../NumberTheory/p-adic-numbers/local-class-field-theory.md), under
which uniformizers act on the maximal unramified extension as the arithmetic Frobenius, is
injective, and the map $W_F^{\mathrm{ab}} \to \mathrm{Gal}(F^{\mathrm{ab}}/F)$ induced by the
inclusion of the Weil group is injective with the same image. So there is a unique isomorphism of
topological groups $\mathrm{Art}_F \colon F^\times \to W_F^{\mathrm{ab}}$ whose image in
$\mathrm{Gal}(F^{\mathrm{ab}}/F)$ is $\mathrm{rec}_F(x)^{-1}$; it sends uniformizers to geometric
Frobenius elements and $\mathcal{O}_F^\times$ onto the image of the inertia group.

**Theorem.** There is a unique family of bijections
$\mathrm{rec}_n \colon \mathcal{A}_n(F) \to \mathcal{G}_n(F)$, $n \ge 1$, such that:

1. $\mathrm{rec}_1(\chi) = \chi \circ \mathrm{Art}_F^{-1}$ for every character $\chi$ of
   $F^\times = \mathrm{GL}_1(F)$;
2. $L(\pi_1 \times \pi_2, s) = L(\mathrm{rec}_{n_1}(\pi_1) \otimes \mathrm{rec}_{n_2}(\pi_2), s)$ and
   $\varepsilon(\pi_1 \times \pi_2, s, \psi) = \varepsilon(\mathrm{rec}_{n_1}(\pi_1) \otimes \mathrm{rec}_{n_2}(\pi_2), s, \psi)$
   for $\pi_i \in \mathcal{A}_{n_i}(F)$, where on the left are the $L$- and $\varepsilon$-factors of
   the pair $(\pi_1, \pi_2)$ and on the right those of the tensor product of Weil–Deligne
   representations;
3. $\mathrm{rec}_n(\pi\chi) = \mathrm{rec}_n(\pi) \otimes \mathrm{rec}_1(\chi)$ for every character
   $\chi$ of $F^\times$;
4. $\det \circ\, \mathrm{rec}_n(\pi) = \mathrm{rec}_1(\omega_\pi)$, where $\omega_\pi$ is the central
   character of $\pi$;
5. $\mathrm{rec}_n(\tilde\pi) = \mathrm{rec}_n(\pi)^\vee$.

The family does not depend on $\psi$. Moreover $\pi$ is supercuspidal (cuspidal) if and only if
$\mathrm{rec}_n(\pi)$ is irreducible, and $\pi$ is essentially square-integrable if and only if
$\mathrm{rec}_n(\pi)$ is indecomposable.

Existence is due to Harris and Taylor and to Henniart; Scholze gave a new proof of the
correspondence between supercuspidal representations and irreducible representations of $W_F$.
Uniqueness is due to Henniart, who showed that such a correspondence between supercuspidal
representations and irreducible representations of $W_F$ is determined by local class field
theory and $\varepsilon$-factors of pairs, and that the whole family is characterized by local
class field theory and $L$- and $\varepsilon$-factors of pairs; Henniart's characterization is
stated for any non-archimedean local field. For local fields of positive characteristic an
analogous correspondence, due to Laumon, Rapoport and Stuhler, rests on local class field theory in
positive characteristic and is not part of this statement.

## Depends on

- [Smooth and admissible representations of p-adic groups](../representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for irreducible admissible representations, twists, central characters and contragredients
- [Cuspidal representations and Jacquet's embedding theorem](../representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for supercuspidal representations
- [Essentially square-integrable representations of GLₙ](essentially-square-integrable-representations-of-gl-n.md)
- [Weil group of a p-adic field](../../../NumberTheory/algebraic-number-theory/galois-representations/weil-deligne-representations/weil-group-of-a-p-adic-field.md), for the Weil group
- [Weil–Deligne representations](../../../NumberTheory/algebraic-number-theory/galois-representations/weil-deligne-representations/weil-deligne-representations.md), for Frobenius-semisimple Weil–Deligne representations and their tensor products, determinants and contragredients
- [Local class field theory](../../../NumberTheory/p-adic-numbers/local-class-field-theory.md), for the local Artin map $\mathrm{rec}_F$ of a finite extension of $\mathbb{Q}_p$; $\mathrm{Art}_F$ is $x \mapsto \mathrm{rec}_F(x)^{-1}$, pointwise inversion (not the inverse map), read in the Weil group, so that uniformizers correspond to geometric Frobenius elements
- [L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](l-and-epsilon-factors-of-pairs.md)

## Proof depends on

- [Construction of the local Langlands correspondence for GLₙ](construction-of-the-local-langlands-correspondence.md), for existence
- [Local converse theorem for GLₙ](local-converse-theorem-for-gl-n.md), for Henniart's theorem that supercuspidal representations are determined by their $\varepsilon$-factors of pairs, which gives uniqueness
- [Langlands classification for GLₙ](langlands-classification-for-gl-n.md), for the reduction to supercuspidal representations
- [L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](l-and-epsilon-factors-of-pairs.md), for the inductive description of the factors in the reduction

## Sources

- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): conventions ($K$ a finite extension of $\mathbb{Q}_p$), (1.1.5)
  (the reciprocity homomorphism $\mathrm{Art}_K \colon K^\times \to \mathrm{Gal}(\bar K/K)^{\mathrm{ab}}$,
  injective with dense image), (1.1.7) (its characterization: uniformizers to geometric Frobenius
  elements and norm groups to the corresponding Galois groups, which identifies it with
  $x \mapsto \mathrm{rec}_K(x)^{-1}$), (1.1.8) (the Weil group), (1.1.10) ("the image of
  $\mathrm{Art}_K$ is $W_K^{\mathrm{ab}}$", an isomorphism of topological groups
  $K^\times \cong W_K^{\mathrm{ab}}$ that maps $\mathcal{O}_K^\times$ onto $I_K^{\mathrm{ab}}$ and
  uniformizers to geometric Frobenius elements), (1.2.1), Theorem (1.2.2)
  (the correspondence and its characterizing properties), Theorem (1.2.3) (1)–(2), (3.1.6)–(3.1.8)
  (Weil–Deligne representations), (4.2.2)–(4.2.3) (reduction to supercuspidal representations;
  uniqueness through Henniart's theorem), and the introduction (Harris–Taylor, Henniart;
  Laumon–Rapoport–Stuhler for local fields of positive characteristic).
- G. Henniart, "Caractérisation de la correspondance de Langlands locale par les facteurs ε de
  paires", Invent. Math. 113 (1993), 339–350,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0113>: the summary and the Corollaire of
  Théorème 1.1.
- G. Henniart, "Une caractérisation de la correspondance de Langlands locale pour GL(n)", Bull. Soc.
  Math. France 130 (2002), 587–602, <http://www.numdam.org/item/BSMF_2002__130_4_587_0/>: §1.1
  ($F$ any non-archimedean local field; the reciprocity map normalized so that geometric Frobenius
  elements correspond to uniformizers; Laumon–Rapoport–Stuhler, Harris–Taylor), §1.3, §1.5 and the
  Corollaire of §1.8 (characterization of the whole family by local class field theory and $L$-
  and $\varepsilon$-factors of pairs).
- P. Scholze, "The local Langlands correspondence for GL_n over p-adic fields", Invent. Math. 192
  (2013), arXiv:1010.1540 (version 1): Theorem 1.2 (c)–(d).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  constructs, at the completions of number fields, a map from irreducible representations of the
  groups $\mathrm{GL}_n$ to Weil–Deligne representations satisfying a restricted list of laws, not
  the full correspondence (`UpperTheory.Zero.LLC.recTExists`).
