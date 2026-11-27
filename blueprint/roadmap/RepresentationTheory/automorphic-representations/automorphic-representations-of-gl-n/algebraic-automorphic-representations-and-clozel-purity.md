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
- **Cohomological representations** (Clozel). A cuspidal regular algebraic representation $\pi$ is
  cohomological after possibly twisting by a quadratic character: there is a quadratic Hecke character
  $\eta$ such that $(\pi \otimes \eta)_\infty$, equivalently every $(\pi \otimes \eta)_v$ with $v \mid \infty$, has
  non-zero $(\mathfrak{g}, K)$-cohomology with coefficients in an algebraic representation,
  $K$ the full maximal compact subgroup, so that it contributes to the cohomology of the locally symmetric
  spaces of $\mathrm{GL}_n$. The twist cannot be omitted: over $\mathbb{Q}$, an odd finite-order Hecke
  character of $\mathrm{GL}_1$ is cuspidal and regular algebraic, but its archimedean component, the sign
  character of $\mathbb{R}^\times$, has zero $(\mathfrak{g}, \mathrm{O}(1))$-cohomology with coefficients in every
  algebraic representation. This is a separate statement from the purity lemma.

## Expansion

A good expansion has pages for the definitions of algebraic, regular algebraic and cohomological
representations, for the purity lemma, and for Clozel's criterion that a cuspidal regular algebraic
representation is cohomological up to a quadratic twist (Lemme 3.14), citing L. Clozel, "Motifs et formes automorphes :
applications du principe de fonctorialité", in *Automorphic Forms, Shimura Varieties, and L-functions*,
Vol. I, Perspect. Math. 10, Academic Press, 1990, 77–159, with locators once it has been consulted, and
the archimedean local Langlands correspondence for $\mathrm{GL}_n$ as a page of its own.

It also writes out these steps of its own proof:

- Clozel's proof of the purity lemma, which Ramakrishnan quotes as a result; its inputs are to be named after reading Clozel (1990), not reconstructed.
- Clozel's Lemme 3.14, as Buzzard and Gee report it (§7.2, p. 37): a regular algebraic cuspidal representation of $\mathrm{GL}_n$ is cohomological after possibly twisting by a quadratic character, which the third item uses; Ramakrishnan's introduction quotes purity, not this.

## Depends on

- [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for the archimedean components, their infinitesimal characters and their $(\mathfrak{g}, K)$-modules
- [Tensor product theorem for automorphic representations](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the archimedean components $\pi_v$ of an automorphic representation
- [Weil groups of local fields and the archimedean local Langlands correspondence for GLₙ](../../reductive-groups-over-local-fields/weil-groups-and-the-archimedean-local-langlands-correspondence.md), for the archimedean local Langlands correspondence for $\mathrm{GL}_n$, which attaches $\sigma_v$ to $\pi_v$; the algebraicity, regularity and weight conditions are conditions on $\sigma_v$

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Sources

- K. Buzzard and T. Gee, "The conjectural connections between automorphic representations and Galois
  representations", arXiv:1009.0785 (version 3): §7.2, p. 37 ("for $\mathrm{GL}_n$ any regular C-algebraic
  representation is cohomological after possibly twisting by a quadratic character (see Lemme 3.14 of
  [Clo90])") and Definition 7.2.1 (cohomological representations).
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
