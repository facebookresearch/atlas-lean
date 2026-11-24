# Algebraic automorphic representations and Clozel's purity lemma

This node is still to be broken down. It covers the archimedean algebraicity conditions of Clozel for
automorphic representations of $\mathrm{GL}_n(\mathbb{A}_F)$ over a number field $F$, and the results on
cuspidal algebraic representations that the theory of automorphic Galois representations uses. For an
archimedean place $v$, let $\sigma_v$ be the $n$-dimensional representation of the Weil group $W_{F_v}$
attached to $\pi_v$ by the archimedean local Langlands correspondence.

- **Algebraic and regular representations.** An automorphic representation $\pi$ is algebraic if at
  every archimedean place the restriction to $\mathbb{C}^\times$ of $\sigma_v \otimes \lvert \cdot \rvert^{(n-1)/2}$ is a direct
  sum of characters $z \mapsto z^{p_j} \bar z^{q_j}$ with $p_j, q_j \in \mathbb{Z}$; it is regular if moreover the
  restriction of $\sigma_v$ to $\mathbb{C}^\times$ is multiplicity free at every archimedean $v$. In terms of the
  infinitesimal character, algebraicity says that its eigenvalues at each embedding $\tau \colon F \to \mathbb{C}$ lie
  in $\mathbb{Z} + \tfrac{n-1}{2}$.
- **Purity lemma** (Clozel). For a cuspidal algebraic $\pi$, regular or not, there is an integer $w$ such
  that $p_j + q_j = w$ for all $j$ at every archimedean place, for the exponents $p_j$, $q_j$ of the twisted
  parameter $\sigma_v \otimes \lvert \cdot \rvert^{(n-1)/2}$. For the untwisted parameter $\sigma_v$, whose restriction to $\mathbb{C}^\times$ is a
  sum of characters $z \mapsto z^{a_j} \bar z^{b_j}$ with $a_j = p_j - \tfrac{n-1}{2}$ and $b_j = q_j - \tfrac{n-1}{2}$, this reads
  $a_j + b_j = w - (n-1)$. Over a totally complex field, for the infinitesimal characters at an embedding
  $\tau$ and at its conjugate $\bar\tau$, the corresponding statement is a symmetry $z \mapsto w' - z$ for an integer
  $w'$ determined by $w$ and $n$ through this shift.
- **Cohomological representations** (Clozel). A cuspidal regular algebraic representation is
  cohomological: its archimedean component has non-zero $(\mathfrak{g}, K)$-cohomology with coefficients in an
  algebraic representation, so that it contributes to the cohomology of the locally symmetric spaces of
  $\mathrm{GL}_n$. This is a separate statement from the purity lemma.

A good expansion has pages for the definitions of algebraic, regular algebraic and cohomological
representations, for the purity lemma, and for the equivalence of regular algebraicity and
cohomologicality for cuspidal representations, citing L. Clozel, "Motifs et formes automorphes :
applications du principe de fonctorialité", in *Automorphic Forms, Shimura Varieties, and L-functions*,
Vol. I, Perspect. Math. 10, Academic Press, 1990, 77–159, with locators once it has been consulted, and
the archimedean local Langlands correspondence for $\mathrm{GL}_n$ as a page of its own.

## Depends on

- [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for the archimedean components, their infinitesimal characters and their $(\mathfrak{g}, K)$-modules
- [Tensor product theorem for automorphic representations](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the archimedean components $\pi_v$ of an automorphic representation

## Sources

- D. Ramakrishnan, "Decomposition and parity of Galois representations attached to GL(4)",
  arXiv:1301.1668 (version 2): introduction, p. 1 (isobaric algebraic representations "([Cℓ1])", regular
  representations, the fixed archimedean weight $w$ defined by the restriction to $\mathbb{C}^*$ of
  $\sigma_v \otimes \lvert \cdot \rvert^{(n-1)/2}$, and "Every cuspidal algebraic π has such a weight ([Cℓ1])"),
  where [Cℓ1] is Clozel's article cited above.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states forms of these results over totally complex and CM fields as
  `GlobalTheory.Published.ClozelPurity`, `GlobalTheory.Published.ClozelCohomological` and
  `GlobalTheory.Published.RegularAlgebraicPurity`.
