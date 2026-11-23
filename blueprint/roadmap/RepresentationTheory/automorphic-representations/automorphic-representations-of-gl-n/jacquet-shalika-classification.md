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
   the cuspidal support.
2. **Satake parameters.** In particular, let $(\pi_i)_{i \in I}$ and $(\pi'_j)_{j \in J}$ be finite families of
   cuspidal automorphic representations of groups $\mathrm{GL}_{m_i}(\mathbb{A})$ and $\mathrm{GL}_{m'_j}(\mathbb{A})$.
   If for almost all finite places $v$ all $\pi_{i,v}$ and $\pi'_{j,v}$ are unramified and the multisets of
   Satake parameters satisfy $\sum_i A(\pi_{i,v}) = \sum_j A(\pi'_{j,v})$, then there is a bijection
   $s \colon I \to J$ with $m_i = m'_{s(i)}$ and $\pi_i \simeq \pi'_{s(i)}$.

## Depends on

- [Automorphic representations as constituents of induced representations](../automorphic-forms-on-reductive-groups/automorphic-representations-as-constituents-of-induced-representations.md), for the cuspidal support $(\tau_1, \dots, \tau_r)$
- [Tensor product theorem for automorphic representations](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the local components $\pi_v$
- [Borel–Casselman theorem on Iwahori-fixed vectors](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/borel-casselman-theorem.md), for unramified representations as constituents of unramified principal series, whose characters give the Satake parameters

## Proof depends on

- [Rankin–Selberg L-functions for GLₙ × GLₘ](rankin-selberg-l-functions-for-gl-n.md), for the location of the poles of $L(s, \tau_i \times \tilde\tau'_j)$ and the convergence and non-vanishing of the partial Rankin–Selberg $L$-functions on $\operatorname{Re} s \ge 1$, through which Jacquet and Shalika compare the orders of the poles at $s = 1$
- [Automorphic representations as constituents of induced representations](../automorphic-forms-on-reductive-groups/automorphic-representations-as-constituents-of-induced-representations.md), for the description of the local components of a constituent of $\mathrm{Ind}(\tau_1 \otimes \dots \otimes \tau_r)$, unramified with Satake parameters $\sum_i A(\tau_{i,v})$ at almost all places, which reduces item 2 to item 1

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 9, §8 (Langlands's
  theorem, "a consequence of the theory of Eisenstein series", and Theorem 9.4, Generalized Strong
  Multiplicity One, "the cuspidal support of $\pi$ is well defined", with the isobaric representations), and
  its reference [3], H. Jacquet and J. A. Shalika, "On Euler products and the classification of automorphic
  forms II", Amer. J. Math. 103 (1981), 777–815.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states item 2 over totally complex fields as `GlobalTheory.Published.JacquetShalikaRigidity`, a component of
  `GlobalTheory.Published.JacquetShalika`.
