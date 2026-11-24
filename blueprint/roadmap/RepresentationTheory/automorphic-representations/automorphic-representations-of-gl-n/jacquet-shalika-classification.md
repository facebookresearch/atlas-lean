# Jacquet–Shalika classification of automorphic representations of GLₙ

Let $k$ be a number field. By Langlands's theorem on
[constituents of induced representations](../automorphic-forms-on-reductive-groups/automorphic-representations-as-constituents-of-induced-representations.md),
every automorphic representation $\pi$ of $\mathrm{GL}_n(\mathbb{A})$ is a constituent of a representation
$\mathrm{Ind}_{Q(\mathbb{A})}^{\mathrm{GL}_n(\mathbb{A})}(\tau_1 \otimes \dots \otimes \tau_r)$, normalized induction (with the square root of the modulus
character), from cuspidal
automorphic representations $\tau_i$ of $\mathrm{GL}_{n_i}(\mathbb{A})$, $n_1 + \dots + n_r = n$, along the
standard parabolic subgroup $Q$ of type $(n_1, \dots, n_r)$.

1. **Generalized strong multiplicity one** (Jacquet–Shalika). Let $\pi$ and $\pi'$ be automorphic
   representations of $\mathrm{GL}_n(\mathbb{A})$, constituents of representations induced from
   $(\tau_1, \dots, \tau_r)$ and $(\tau'_1, \dots, \tau'_{r'})$ as above. If $\pi_v \simeq \pi'_v$ for all $v$
   outside a finite set $S$, then $r = r'$ and there is a permutation $\sigma$ of $\{1, \dots, r\}$ with
   $n_i = n'_{\sigma(i)}$ and $\tau_i \simeq \tau'_{\sigma(i)}$: the local components at almost all places determine
   the cuspidal support. This does not separate the different constituents of one induced representation.
2. **Isobaric sums** (Langlands; Jacquet–Shalika). For cuspidal automorphic representations $\tau_i$ of
   $\mathrm{GL}_{n_i}(\mathbb{A})$, not necessarily unitary, there is an automorphic representation
   $\pi = \tau_1 \boxplus \dots \boxplus \tau_r$ of $\mathrm{GL}_n(\mathbb{A})$, a constituent of $\mathrm{Ind}(\tau_1 \otimes \dots \otimes \tau_r)$, whose local
   component at every place $v$ has as $L$-parameter the direct sum of the $L$-parameters of the $\tau_{i,v}$:
   $\pi_v$ is the Langlands quotient of the standard module obtained by writing each $\tau_{i,v}$ through its own
   standard data and ordering all the resulting essentially tempered pieces by decreasing real exponent. It
   depends only on the multiset $\{\tau_1, \dots, \tau_r\}$, and by item 1 an isobaric sum is determined by its local
   components at almost all places. For example, the trivial representation of $\mathrm{GL}_2(\mathbb{A})$ is the isobaric
   sum $\lvert \cdot \rvert^{1/2} \boxplus \lvert \cdot \rvert^{-1/2}$ of two characters that are not unitary.
3. **Satake parameters.** In particular, let $(\pi_i)_{i \in I}$ and $(\pi'_j)_{j \in J}$ be finite families of
   cuspidal automorphic representations of groups $\mathrm{GL}_{m_i}(\mathbb{A})$ and $\mathrm{GL}_{m'_j}(\mathbb{A})$.
   If for almost all finite places $v$ all $\pi_{i,v}$ and $\pi'_{j,v}$ are unramified and the multisets of
   Satake parameters satisfy $\sum_i A(\pi_{i,v}) = \sum_j A(\pi'_{j,v})$, then there is a bijection
   $s \colon I \to J$ with $m_i = m'_{s(i)}$ and $\pi_i \simeq \pi'_{s(i)}$.

## Depends on

- [Automorphic representations as constituents of induced representations](../automorphic-forms-on-reductive-groups/automorphic-representations-as-constituents-of-induced-representations.md), for the cuspidal support $(\tau_1, \dots, \tau_r)$
- [Tensor product theorem for automorphic representations](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the local components $\pi_v$
- [Borel–Casselman theorem on Iwahori-fixed vectors](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/borel-casselman-theorem.md), for unramified representations as constituents of unramified principal series, whose characters give the Satake parameters
- [Langlands classification for GLₙ](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/langlands-classification-for-gl-n.md), for Langlands quotients at the finite places in item 2
- [Characters, principal series and the Langlands classification for real reductive groups](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/principal-series-of-real-reductive-groups.md), for Langlands quotients at the infinite places in item 2

## Proof depends on

- [Rankin–Selberg L-functions for GLₙ × GLₘ](rankin-selberg-l-functions-for-gl-n.md), for item 1, following Jacquet and Shalika (II, Theorems (4.1)–(4.4)): writing each cuspidal datum as $\sigma_j \lvert \det \rvert^{t_j}$ with $\sigma_j$ unitary and $t_j$ real, one shifts the smallest real exponent to $0$ and pairs with a unitary datum of that exponent; the data with larger exponents contribute partial $L$-functions in the open half-plane $\operatorname{Re} s > 1$, where they converge absolutely and do not vanish, and on the minimal layer the comparison at the point $s = 1$ uses the actual simple pole of $L^S(s, \sigma \times \tilde\sigma)$ there, together with the fact that every cross term $L^S(s, \sigma \times \tilde\sigma')$ with $\sigma' \not\simeq \sigma$ (of the same or of another rank) is finite and non-zero at $s = 1$ (the non-vanishing on $\operatorname{Re} s = 1$ away from the poles, stated on the Rankin–Selberg page): for an imaginary twist $\sigma' = \sigma \lvert \det \rvert^{it}$, $t \ne 0$, the pole is at $1 + it$, not at $1$ (for $\sigma = 1$ on $\mathrm{GL}_1$ the cross term is $\zeta^S(s - it)$), so only the datum isomorphic to $\sigma$ contributes a pole at $1$; the multiplicities are then recovered from the power sums $\mathrm{tr}(A_v^\ell)$, $\ell \ge 1$, at all good places
- [Automorphic representations as constituents of induced representations](../automorphic-forms-on-reductive-groups/automorphic-representations-as-constituents-of-induced-representations.md), for the local components of a constituent of $\mathrm{Ind}(\tau_1 \otimes \dots \otimes \tau_r)$, unramified with Satake parameters $\sum_i A(\tau_{i,v})$ at almost all places, which reduces item 3 to item 1 (Jacquet and Shalika prove both from their Theorem (4.2)); and, for item 2, the realization of the constituents of $\mathrm{Ind}(\tau_1 \otimes \dots \otimes \tau_r)$ in spaces of automorphic forms through Taylor coefficients of pole-cleared Eisenstein series
- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for the Eisenstein series of item 2
- [Langlands classification for GLₙ](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/langlands-classification-for-gl-n.md), for the Langlands quotients of the local standard modules at the finite places (item 2)
- [Characters, principal series and the Langlands classification for real reductive groups](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/principal-series-of-real-reductive-groups.md), for the Langlands quotients at the infinite places (item 2)

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 9, §8 (Langlands's
  theorem, "a consequence of the theory of Eisenstein series", and Theorem 9.4, Generalized Strong
  Multiplicity One, "the cuspidal support of $\pi$ is well defined", with the isobaric representations), and
  its reference [3], H. Jacquet and J. A. Shalika, "On Euler products and the classification of automorphic
  forms II", Amer. J. Math. 103 (1981), 777–815: §3.7, p. 804 (non-vanishing on $\operatorname{Re} s = 1$ away from the poles,
  attributed to Shahidi), Theorems (4.1)–(4.4), pp. 804–809 (the comparison with the shifted minimal real
  exponent and the recovery of multiplicities), §4, (4.4) and (4.5) (the essentially unique cuspidal
  support, and, through the theory of Eisenstein series, the automorphic representation attached to a
  formal sum of cuspidal representations).
- H. Jacquet and J. A. Shalika, "On Euler products and the classification of automorphic representations
  I", Amer. J. Math. 103 (1981), 499–558: §0.3, p. 503 (normalized induction).
- T. Kaletha, A. Mínguez, S. W. Shin and P.-J. White, "Endoscopic classification of representations: inner
  forms of unitary groups", arXiv:1409.3731: §1.3.2, (1.3.1)–(1.3.3) (isobaric sums, defined by the
  Langlands quotient of the normalized induction at every place, with $L$-parameter the direct sum of those of
  the summands; determination by almost all places through the Jacquet–Shalika theorem).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states item 3 over totally complex fields, for finite families of positive ranks and cofinitely many finite
  places, as `GlobalTheory.Published.JacquetShalikaRigidity`, a component of `GlobalTheory.Published.JacquetShalika`.
