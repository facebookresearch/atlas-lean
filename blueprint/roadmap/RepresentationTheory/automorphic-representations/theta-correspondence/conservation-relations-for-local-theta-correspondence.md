# Conservation relations for the local theta correspondence

This node is still to be broken down. It covers the conservation relations of Sun and Zhu for the first occurrence of
local theta lifts in two Witt towers, which the doubling method uses. Let $F$ be a local field of characteristic zero,
$D$ either $F$, a quadratic extension of $F$ or a quaternion algebra over $F$, $U$ an $\epsilon$-Hermitian right $D$-vector
space, and $\bar G(U)$ the group acting in the oscillator representations: the metaplectic cover of the isometry group
when $U$ is symplectic, the isometry group otherwise.

- **Enhanced oscillator representations and Witt towers.** An enhanced oscillator representation of $\bar G(U)$ is a pair
  $\sigma = (V, \omega)$ of a $-\epsilon$-Hermitian left $D$-vector space $V$ and a smooth oscillator representation $\omega$ of
  $\bar G(U) \ltimes \mathrm{H}(U \otimes_D V)$, genuine in the sense that, when $U$ is symplectic, the nontrivial central element
  $\varepsilon_U$ of the cover acts by $(-1)^{\dim V}$. These pairs form a commutative monoid under orthogonal sum, with a
  hyperbolic plane $\mathrm{H}_U$. Two pairs are Witt equivalent if they become isomorphic after adding multiples of
  $\mathrm{H}_U$, and the classes, the Witt towers, form an abelian group $\mathcal{W}_U$.
- **First occurrence.** An irreducible representation $\pi$ of $\bar G(U)$ occurs in $\sigma = (V, \omega)$ if
  $\mathrm{Hom}_{\bar G(U)}(\omega, \pi) \ne 0$; it is genuine with respect to a Witt tower $t$ if, when $U$ is symplectic,
  $\varepsilon_U$ acts on $\pi$ by $(-1)^{\dim \sigma}$ for $\sigma$ in $t$. For such $\pi$ the first occurrence index $n_t(\pi)$ is the least
  $\dim \sigma$ with $\sigma$ in $t$ in which $\pi$ occurs. It is finite, since $\pi$ occurs once the split rank of $\sigma$ is at least
  $\dim U$, and occurrence persists up a tower (Kudla).
- **Constants.** $d_{D,\epsilon}$ is the largest dimension of an anisotropic $-\epsilon$-Hermitian space: $0$, $1$, $2$, $3$ or $4$ when
  these spaces are symplectic, quaternionic Hermitian, Hermitian or skew-Hermitian, quaternionic skew-Hermitian, or
  symmetric bilinear. The anti-split Witt tower $t^\circ_U \in \mathcal{W}_U$ is characterized by
  $n_{t^\circ_U}(1_U) = 2 \dim U + d_{D,\epsilon}$ for the trivial representation $1_U$.
- **Non-archimedean case** (Sun–Zhu, Theorem 1.10). Let $F$ be non-archimedean. If $t_1, t_2 \in \mathcal{W}_U$ differ by
  $t^\circ_U$, then $n_{t_1}(\pi) + n_{t_2}(\pi) = 2 \dim U + d_{D,\epsilon}$ for every irreducible $\pi$ genuine with respect to $t_1$
  (hence with respect to $t_2$). The inequality $\ge$ is due to Rallis and to Kudla and Rallis for orthogonal–symplectic
  dual pairs, and to Gong and Grenié, following Harris, Kudla and Sweet, for unitary dual pairs.
- **Archimedean case** (Sun–Zhu, Theorem 7.6). Let $U$ be a real symplectic space, a complex Hermitian or
  skew-Hermitian space, or a real quaternionic skew-Hermitian space, $K_U \subseteq \mathcal{W}_U$ the cyclic subgroup of Sun and
  Zhu's §7, the image of the kernel of the Kudla homomorphism, and $T$ a coset of $K_U$. For every irreducible $\pi$
  genuine with respect to the elements of $T$, there exist two different $t_1, t_2 \in T$ with
  $n_{t_1}(\pi) + n_{t_2}(\pi) = 2 \dim U + d_{D,\epsilon}$, and $n_{t_3}(\pi) + n_{t_4}(\pi) \ge 2 \dim U + d_{D,\epsilon} \lvert t_3 - t_4 \rvert$ for
  all different $t_3, t_4 \in T$, where $\lvert t \rvert$ is the multiple of a generator of $K_U$ that $t$ is. The equality holds for
  some pair in $T$, not for every pair.
- **Unitary dual pairs.** In particular, let $E/F$ be a quadratic extension of local fields of characteristic zero, $U$ a
  skew-Hermitian space of dimension $n$ over $E$, and $\pi$ an irreducible representation of $\mathrm{U}(U)$. If $\pi$ has nonzero
  theta lifts, for the same additive character and the same splitting character, to Hermitian spaces $V$ and $V'$ in
  different Witt towers, then $\dim V + \dim V' \ge 2n + 2$: the dimensions are at least the first occurrence indices of
  the two towers, which differ by $t^\circ_U$ in the non-archimedean case and lie in one coset of $K_U$ in the archimedean
  case.

## Expansion

A good expansion has definition pages for enhanced oscillator representations, Witt towers, genuineness, occurrence,
first occurrence indices, the anti-split tower and the subgroup $K_U$, and statement pages for the two theorems and for
the unitary consequence, each citing the sources below with locators. Sun and Zhu obtain the upper bound from the
occurrence given by the doubling method (Corollary 5.7) and the lower bound from the non-occurrence of the trivial
representation before the stable range (Proposition 6.2), as their §2.1 explains.

## Depends on

- [Metaplectic group and the local Weil representation](metaplectic-group-and-local-weil-representation.md), for the oscillator representations of Heisenberg groups and metaplectic groups, from which the enhanced oscillator representations are built

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- B. Sun and C.-B. Zhu, "Conservation relations for local theta correspondence", arXiv:1204.2969 (version 3): §1.1
  (dual pairs of type I over local fields of characteristic zero), Proposition 1.6, (4), p. 5 ($d_{D,\epsilon}$), §1.4 and
  Definition 1.8, pp. 5–7 (enhanced oscillator representations and Witt towers), §1.5, (7)–(9) and Theorem 1.10, pp. 7–8,
  with Remarks (a)–(c) (the attributions of the inequality), §2.1 (Corollary 5.7 and Proposition 6.2), and §7, (82) and
  Theorem 7.6, (84)–(85), pp. 44–45.
