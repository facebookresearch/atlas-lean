# Jacquet–Shalika classification of automorphic representations of GLₙ

Let $k$ be a number field. By Langlands's theorem on
[constituents of induced representations](../automorphic-forms-on-reductive-groups/automorphic-representations-as-constituents-of-induced-representations.md),
every automorphic representation $\pi$ of $\mathrm{GL}_n(\mathbb{A})$ is a constituent of a representation
$\mathrm{Ind}_{Q(\mathbb{A})}^{\mathrm{GL}_n(\mathbb{A})}(\tau_1 \otimes \dots \otimes \tau_r)$ induced from cuspidal
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
   $\pi = \tau_1 \boxplus \dots \boxplus \tau_r$ of $\mathrm{GL}_n(\mathbb{A})$ whose local component at every place $v$ is the Langlands
   quotient of the normalized parabolic induction from $\tau_{1,v} \otimes \dots \otimes \tau_{r,v}$ (taken in the order
   given by the real parts of the central exponents); it is constructed from residues and values of
   Eisenstein series, it depends only on the multiset $\{\tau_1, \dots, \tau_r\}$, and by item 1 an isobaric sum is
   determined by its local components at almost all places. The isobaric sums of unitary cuspidal
   representations contain the unitary cuspidal ones and, by the classification of Mœglin and Waldspurger,
   the discrete spectrum.
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

- [Rankin–Selberg L-functions for GLₙ × GLₘ](rankin-selberg-l-functions-for-gl-n.md), for the absolute convergence and non-vanishing of the partial Rankin–Selberg $L$-functions of unitary cuspidal representations in $\operatorname{Re} s > 1$ and the location and order of their poles at $s = 1$ after twisting by $\lvert \det \rvert^{it}$; Jacquet and Shalika order the real twists of the cuspidal data and compare orders of poles of products of such $L$-functions to recover the multiset of cuspidal data (item 1)
- [Automorphic representations as constituents of induced representations](../automorphic-forms-on-reductive-groups/automorphic-representations-as-constituents-of-induced-representations.md), for the local components of a constituent of $\mathrm{Ind}(\tau_1 \otimes \dots \otimes \tau_r)$, unramified with Satake parameters $\sum_i A(\tau_{i,v})$ at almost all places, which reduces item 3 to item 1
- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for the construction of the isobaric sum through Eisenstein series (item 2)
- [Langlands classification for GLₙ](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/langlands-classification-for-gl-n.md), for the Langlands quotients of the local induced representations at the finite places (item 2)

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 9, §8 (Langlands's
  theorem, "a consequence of the theory of Eisenstein series", and Theorem 9.4, Generalized Strong
  Multiplicity One, "the cuspidal support of $\pi$ is well defined", with the isobaric representations), and
  its reference [3], H. Jacquet and J. A. Shalika, "On Euler products and the classification of automorphic
  forms II", Amer. J. Math. 103 (1981), 777–815: §4, (4.4) and (4.5) (the essentially unique cuspidal
  support, and, through the theory of Eisenstein series, the automorphic representation attached to a
  formal sum of cuspidal representations).
- T. Kaletha, A. Mínguez, S. W. Shin and P.-J. White, "Endoscopic classification of representations: inner
  forms of unitary groups", arXiv:1409.3731: §1.3.2, (1.3.1)–(1.3.3) (isobaric sums, defined by the
  Langlands quotient of the normalized induction at every place; the discrete spectrum of $\mathrm{GL}(N)$
  after Mœglin and Waldspurger; determination by almost all places through the Jacquet–Shalika theorem).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states item 2 over totally complex fields as `GlobalTheory.Published.JacquetShalikaRigidity`, a component of
  `GlobalTheory.Published.JacquetShalika`.
