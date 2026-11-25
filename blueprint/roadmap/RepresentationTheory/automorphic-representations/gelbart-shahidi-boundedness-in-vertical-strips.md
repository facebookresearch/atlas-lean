# Boundedness in vertical strips of Langlands–Shahidi L-functions

This node is still to be broken down. It covers the theorem of Gelbart and Shahidi that the automorphic $L$-functions of
the Langlands–Shahidi method are bounded in vertical strips of finite width, under a condition on normalized local
intertwining operators, which the Rankin–Selberg $L$-functions of $\mathrm{GL}_n \times \mathrm{GL}_m$ use when $m < n - 1$. It states the
theorem in the form that Shahidi's ICM report gives it. Let $F$ be a number field, $\mathbf{G}$ a quasi-split reductive group over
$F$, $\mathbf{P} = \mathbf{M}\mathbf{N}$ a maximal parabolic subgroup, $\pi$ a globally generic cuspidal automorphic representation of
$\mathbf{M}(\mathbb{A}_F)$, and $L(s, \pi, r_i)$, $1 \le i \le m$, the $L$-functions that the Langlands–Shahidi method attaches to the irreducible
constituents $r_i$ of the adjoint action of ${}^L M$ on the Lie algebra of the unipotent radical ${}^L N$ of the parabolic subgroup
${}^L P$ of ${}^L G$ dual to $\mathbf{P}$, through the constant terms and Fourier coefficients of the
[Eisenstein series](automorphic-forms-on-reductive-groups/eisenstein-series.md) induced from $\pi$. At each place $v$ let
$A(s, \pi_v, w_0)$ be the local intertwining operator of the Weyl element $w_0$ that takes $\mathbf{P}$ to its associate, and
$N(s, \pi_v, w_0)$ the normalized operator defined by $A(s, \pi_v, w_0) = r(s, \pi_v, w_0) N(s, \pi_v, w_0)$ with
$r(s, \pi_v, w_0) = \prod_{i=1}^m L(is, \pi_v, r_i) / \big(L(1 + is, \pi_v, r_i) \, \varepsilon(is, \pi_v, r_i, \psi_v)\big)$.

- **Condition (5.1).** For every place $v$, $N(s, \pi_v, w_0)$ is holomorphic and nonzero for $\operatorname{Re} s \ge \tfrac12$.
- **Theorem** (Gelbart–Shahidi, Theorem 4.1, as Shahidi reports it). Assume (5.1). Then each $L(s, \pi, r_i)$ has only finitely
  many poles, and it is bounded in every vertical strip of finite width away from them.
- **Highly ramified twists** (Shahidi, Theorems 5.1 and 5.2). Assume (5.1), and let $\xi(m) = \det(\mathrm{Ad}(m) \mid \mathfrak{n})$. For a
  nonempty finite set $S$ of finite places there are integers $f_v \ge 0$, $v \in S$, depending only on the local central characters
  of $\pi$, such that for every Grössencharacter $\eta$ whose conductor at each $v \in S$ is at least $f_v$, every
  $L(s, \pi_\eta, r_i)$, $\pi_\eta = \pi \otimes (\eta \cdot \xi)$, is entire, and bounded in every vertical strip of finite width.
- **Pairs of general linear groups** (Shahidi, Remark 4.5). For $\mathbf{G} = \mathrm{GL}_{n+m}$, $\mathbf{M} = \mathrm{GL}_n \times \mathrm{GL}_m$ and the
  representation $\pi \otimes \tilde\pi'$ of $\mathbf{M}(\mathbb{A}_F)$, with $\pi$ and $\pi'$ cuspidal representations of $\mathrm{GL}_n(\mathbb{A}_F)$ and
  $\mathrm{GL}_m(\mathbb{A}_F)$, there is one $L$-function, $L(s, \pi \otimes \tilde\pi', r_1) = L(s, \pi \times \pi')$, the Rankin–Selberg
  $L$-function of the pair. If (5.1) holds for these data, $L(s, \pi \times \pi')$ has only finitely many poles and is bounded in
  every vertical strip of finite width away from them.

## Expansion

A good expansion has statement pages for the theorem, for the highly ramified twists and for the case of pairs, citing
the sources below with locators.

It also plans this step, which is not complete:

- the verification of (5.1) for the data $(\mathrm{GL}_{n+m}, \mathrm{GL}_n \times \mathrm{GL}_m, \pi \otimes \tilde\pi')$, which the case of pairs needs, and
  without which that case stays conditional. At a finite place Kim's argument applies: $N(s, \pi_v, w_0)$ factors into rank-one
  normalized operators of the same kind, those attached to tempered data are holomorphic and nonzero for $\operatorname{Re} s > -1$
  (Mœglin and Waldspurger, Kim's Proposition 4.5), and the generic unitary local components are induced from such data
  twisted by exponents of absolute value less than $\tfrac12$ (Tadić, as Kim uses it), so that the shifted parameters stay in that
  region for $\operatorname{Re} s \ge \tfrac12$; the nonvanishing of the product comes from Zhang's lemma (Kim's Lemma 4.7, p. 586), under its
  hypothesis on the rank-one tempered local factors. At the archimedean places no source is recorded yet, and the
  verification remains open there.

## Depends on

- [Eisenstein series and their meromorphic continuation](automorphic-forms-on-reductive-groups/eisenstein-series.md), for the Eisenstein series whose constant terms and Fourier coefficients define these $L$-functions

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in *Lectures on Automorphic
  L-functions*, Fields Institute Monographs 20, American Mathematical Society, 2004; author's version
  <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 9, §5, pp. 72–73 (the finite-sum argument reaches only
  $m = n$ and $m = n - 1$; "Gelbart and Shahidi have proven boundedness in vertical strips for a wide class of
  L-functions, including ours, via the Langlands–Shahidi method").
- F. Shahidi, "Automorphic L-functions and functoriality", in *Proceedings of the International Congress of
  Mathematicians* (Beijing, 2002), arXiv:math/0304329: Remark 4.5, p. 661 (the Levi subgroup $\mathrm{GL}_t \times \mathrm{GL}_n$ of
  $\mathrm{GL}_{t+n}$, one $L$-function, the Rankin–Selberg product), §5, p. 661 (condition (5.1) on the local intertwining
  operators normalized as in Shahidi's 1981 paper), and p. 662 (Theorem 5.1, the highly ramified twists, with
  $\xi(m) = \det(\mathrm{Ad}(m) \mid \mathfrak{n})$; "boundedness of each $L(s, \pi, r_i)$ in every vertical strip of finite width, away
  from its poles, which are finite in number … under Assumption (5.1). This was proved in full generality by
  Gelbart–Shahidi"; "The main theorem of [15] (Theorem 4.1) is in full generality, allowing poles"; Theorem 5.2).
- H. H. Kim, "On local L-functions and normalized intertwining operators", Canad. J. Math. 57 (2005), 535–597: (1.1),
  p. 538 (the normalization $A = rN$), §4, p. 584 (Assumption (A), the same condition for every place), Proposition 4.5,
  p. 585 (the normalized operators for tempered data of $\mathrm{GL}_k \times \mathrm{GL}_l \subset \mathrm{GL}_{k+l}$, after Mœglin and
  Waldspurger), and p. 589 (Tadić's classification of generic unitary representations of $\mathrm{GL}_n$ over a finite place, with
  exponents less than $\tfrac12$, and the reduction to rank-one operators), with Lemma 4.7, p. 586 (Zhang's lemma, for the
  nonvanishing).
