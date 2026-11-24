# Endoscopic classification and base change for unitary groups

This node is still to be broken down. It covers the classification of the discrete automorphic spectrum of
unitary groups in terms of automorphic representations of general linear groups, and the base change
from unitary groups to $\mathrm{GL}_N$ that it gives. Let $E/F$ be a quadratic extension of number fields
and $U_{E/F}(N)$ the quasi-split unitary group in $N$ variables.

- **Global parameters.** Fix $\kappa \in \{\pm 1\}$, a character $\chi_\kappa$ of $\mathbb{A}_E^\times / E^\times$ with the
  corresponding parity, and the $L$-embedding $\xi_{\chi_\kappa}$ of the $L$-group of $U_{E/F}(N)$ into that of
  $\mathrm{R}_{E/F}\mathrm{GL}_N$ it defines. Square-integrable parameters are formal sums
  $\psi = \mu_1 \boxtimes \nu_1 \boxplus \dots \boxplus \mu_r \boxtimes \nu_r$ of distinct pairs, with $\mu_i$ a conjugate self-dual unitary
  [cuspidal automorphic representation](automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md)
  of $\mathrm{GL}_{m_i}(\mathbb{A}_E)$, $\nu_i$ the irreducible representation of $\mathrm{SL}_2(\mathbb{C})$ of dimension $d_i$,
  $\sum_i m_i d_i = N$, and every block of the same sign $\kappa_i(-1)^{N_i - 1} = \kappa(-1)^{N-1}$, where $\kappa_i$ is defined from the
  block (Mok's Remark 2.4.6 and Definition 2.4.7, with $N_i = m_i d_i$). The block $\mu_i \boxtimes \nu_i$ corresponds to the
  discrete automorphic representation $\mu_i \lvert \det \rvert^{(d_i - 1)/2} \boxplus \dots \boxplus \mu_i \lvert \det \rvert^{(1 - d_i)/2}$ of $\mathrm{GL}_{N_i}(\mathbb{A}_E)$
  (Mœglin–Waldspurger; KMSW, (1.3.2)). Each $\psi$ has a global packet and a sign character $\varepsilon_\psi$.
- **Classification** (Mok). For the quasi-split group, the discrete spectrum
  $L^2_{\mathrm{disc}}(U_{E/F}(N)(F) \backslash U_{E/F}(N)(\mathbb{A}_F))$, which contains residual as well as cuspidal
  representations, decomposes as the direct sum over square-integrable parameters $\psi$ of the
  representations $\pi$ of the global packet whose character $\langle \cdot, \pi \rangle$, the product of the local
  packet pairings, equals $\varepsilon_\psi$; the proof rests on the stabilization of the twisted trace formula, the
  Jacquet–Shalika theorem and the classification of the discrete spectrum of $\mathrm{GL}_N$ by Mœglin and
  Waldspurger.
- **Weak base change** (Mok). Every discrete automorphic representation of $U_{E/F}(N)$, and of the unitary
  group $\mathrm{U}(V)$ of any Hermitian space $V$ of dimension $N$ over $E$ (Mok's §10), has a weak base change
  with respect to $\xi_{\chi_\kappa}$: an isobaric automorphic representation of $\mathrm{GL}_N(\mathbb{A}_E)$ with matching
  Satake parameters at almost all places.
- **Inner forms** (Kaletha–Mínguez–Shin–White). The decomposition of the discrete spectrum for inner
  twists of $U_{E/F}(N)$: their paper proves it unconditionally for generic parameters and pure inner twists,
  and in general under two hypotheses whose resolution it announces for sequels.
- **Base change package for the standard definite unitary group** (pending). Let $E$ be a CM field
  unramified at every finite place over its maximal totally real subfield $F$, $n \ge 1$, and $\mathrm{U}_n$ the unitary
  group of the identity Hermitian matrix. For every automorphic representation $\pi$ of $\mathrm{U}_n(\mathbb{A}_F)$ the package
  asserts the existence of: positive integers $N_1, \dots, N_c$ with sum $n$; discrete automorphic representations
  $\Pi_i$ of $\mathrm{GL}_{N_i}(\mathbb{A}_E)$, each the block $\mu_i \lvert \det \rvert^{(d_i - 1)/2} \boxplus \dots \boxplus \mu_i \lvert \det \rvert^{(1 - d_i)/2}$ attached to a unitary,
  conjugate self-dual cuspidal $\mu_i$ and a length $d_i$ (possibly $d_i > 1$: the block is conjugate self-dual,
  its shifted terms are not, except the middle term $\mu_i$ when $d_i$ is odd); local components $\Pi_{i,w}$ at the finite places $w$ of $E$ and infinitesimal
  characters at the archimedean places; and, at every finite place $w$, an irreducible representation $P_w$ of
  $\mathrm{GL}_n(E_w)$ that is a subquotient of the representation induced from the $\Pi_{i,w}$, such that: $P_w$ is spherical
  where $\pi$ is unramified; at a place where $E/F$ is inert and unramified and $\pi_w$ has Satake parameter $\alpha$, $P_w$
  has the Satake parameter given by unramified base change of $\alpha$ (a conditional relation: it says nothing
  when $\pi_w$ is not spherical, which the unramifiedness of the extension does not exclude); at the split places,
  $\pi_w$ and $P_w$ correspond through $\mathrm{U}_n(F_v) \cong \mathrm{GL}_n(E_w)$; and at each archimedean place the multiset union of the
  infinitesimal characters of the $\Pi_i$ is the infinitesimal character determined by the weight of $\pi$. The
  blocks cannot in general be cuspidal: for the trivial representation of the definite $\mathrm{U}(2)$ over
  $\mathbb{Q}(\zeta_{12}) / \mathbb{Q}(\sqrt 3)$, which is unramified at every finite place, the components at the split places are
  trivial representations of $\mathrm{GL}_2$, neither generic nor the isobaric sum of two conjugate self-dual
  characters. The package does not identify the local $L$-parameters of the components of $\pi$ at ramified
  inert places, and its archimedean condition is an identity of infinitesimal characters, not of
  representations. It is stronger than weak base change, which only matches almost all places, and should
  be sourced with locators before it is relied upon, for instance from Labesse's work on base change for
  definite unitary groups or from the local–global compatibility in the endoscopic classification; any
  stronger statement identifying all local components needs its own source.

## Expansion

A good expansion has pages for the global parameters and their localizations, the local and global
packets and the sign character, the classification for quasi-split unitary groups, the weak base change,
and the classification and base change for inner forms, with the conditional status of each statement
recorded; the base change for definite unitary groups should also be checked against J.-P. Labesse,
"Changement de base CM et séries discrètes", in *On the Stabilization of the Trace Formula*, International
Press, 2011, with locators.

A good expansion also writes out these steps of its own proof:

- the identification of the Asai $L$-function with the pole, $\mathrm{Asai}^\eta$ with $\eta = (-1)^{N-1}\kappa$ (Mok, Theorem 2.5.4 (a), p. 36, and Remark 2.5.6), for the parity: the simple pole of the product alone determines neither.
- for the quasi-split groups, Mok's comparison of the stabilized trace formula of $U_{E/F}(N)$ with the stabilized twisted trace formula of $\mathrm{R}_{E/F}\mathrm{GL}_N$, and the analysis of the parity that it gives; the classification is conditional on the stabilizations it compares.
- for inner forms, the comparison of the untwisted trace formula of the inner twist with Mok's results (KMSW, Theorem* 1.7.1, p. 89, and Chapter 5, Theorem 5.0.5, pp. 205–206), which holds under the two local hypotheses at every place and the stabilization of that trace formula.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for automorphic and cuspidal automorphic representations
- [Jacquet–Shalika classification of automorphic representations of GLₙ](automorphic-representations-of-gl-n/jacquet-shalika-classification.md), for isobaric sums of cuspidal representations of general linear groups
- [Discreteness of the cuspidal spectrum](automorphic-forms-on-reductive-groups/discreteness-of-the-cuspidal-spectrum.md), for the cuspidal part of the discrete spectrum (the residual part is described through Eisenstein series)
- [Eisenstein series and their meromorphic continuation](automorphic-forms-on-reductive-groups/eisenstein-series.md), for the residual spectrum

## Proof depends on

- [Jacquet–Shalika classification of automorphic representations of GLₙ](automorphic-representations-of-gl-n/jacquet-shalika-classification.md), for the bijection between the parameters $\psi$ and the families of Satake parameters they determine, which with Mœglin–Waldspurger's theorem Mok uses to separate the global parameters (Mok, Example 4.3.1, (4.3.5))
- [Rankin–Selberg L-functions for GLₙ × GLₘ](automorphic-representations-of-gl-n/rankin-selberg-l-functions-for-gl-n.md), for the simple pole at $s = 1$ of the Rankin–Selberg $L$-function of a conjugate self-dual cuspidal representation and its contragredient, the product of its two Asai $L$-functions (Mok, (2.5.9), pp. 35–36), which underlies the parity of these representations
- [Asai L-functions at s = 1](automorphic-representations-of-gl-n/asai-l-functions-at-s-equal-one.md), for the non-vanishing at $s = 1$ of both Asai $L$-functions (Shahidi, as Mok cites it, p. 36), by which exactly one of them has a pole there, a simple one, for the parity
- [Mœglin–Waldspurger classification of the discrete spectrum of GLₙ](automorphic-representations-of-gl-n/moeglin-waldspurger-classification-of-the-discrete-spectrum.md), for Mœglin–Waldspurger's classification of the discrete spectrum of $\mathrm{GL}_N$ by the blocks attached to a unitary cuspidal $\mu$ and a length $d \ge 1$, cuspidal for $d = 1$ and residual for $d > 1$ (KMSW, (1.3.2)–(1.3.3), p. 64)
- [Stabilization of the trace formulas for unitary groups and their twisted comparison group](stabilization-of-trace-formulas-for-unitary-groups.md), for the stabilizations that Mok's comparison and that of Kaletha, Mínguez, Shin and White rest on: of the twisted trace formula of $\mathrm{R}_{E/F}\mathrm{GL}_N$ (Mok's Hypothesis 4.2.1) and of the trace formulas of $U_{E/F}(N)$ and of its inner twists, with the transfer and the standard and weighted fundamental lemmas
- [Local classification and the local intertwining relation for inner forms of unitary groups](../reductive-groups-over-local-fields/local-classification-and-intertwining-relation-for-unitary-groups.md), for the local classification and the local intertwining relation at every place, the two hypotheses of Kaletha, Mínguez, Shin and White's Theorem 5.0.5 for inner forms

## Sources

- C. P. Mok, "Endoscopic classification of representations of quasi-split unitary groups", Mem.
  Amer. Math. Soc. 235 (2015), no. 1108, arXiv:1206.0882 (version 5): introduction, §2.3 (formal global
  parameters $\mu \boxtimes \nu$), Definition 2.4.7 (square-integrable parameters and their parity
  condition), Theorem 2.5.2 (decomposition of the discrete spectrum), §2.6 (the stabilization of the twisted
  trace formula), §4.3 with display (4.3.5), Corollary 4.3.8 and the paragraph after it ("corollary 4.3.8
  gives in particular the existence of 'weak base change' associated to discrete automorphic
  representations on $U_{E/F}(N)$ (with respect to the L-embedding $\xi$)"), and §10, Proposition 10.0.1 and
  Corollary 10.0.2 (the same for the unitary groups of Hermitian spaces).
- T. Kaletha, A. Mínguez, S. W. Shin and P.-J. White, "Endoscopic classification of representations: inner
  forms of unitary groups", arXiv:1409.3731: §1.3.2, (1.3.1)–(1.3.3), pp. 64–65 (isobaric sums and the discrete
  spectrum of $\mathrm{GL}(N)$, after Mœglin and Waldspurger, as the blocks $\mu \lvert \det \rvert^{(d-1)/2} \boxplus \dots \boxplus \mu \lvert \det \rvert^{(1-d)/2}$),
  Theorem* 1.7.1 (the decomposition for inner twists of
  $U_{E/F}(N)$) and the paragraph after it (proved in Chapter 5 under two hypotheses, whose resolution is
  announced for the sequels [KMSa], [KMSb]; unconditional for generic parameters and pure inner twists).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the package of the pending item, with discrete conjugate self-dual blocks, local subquotients at the
  finite places, the split comparison, the conditional inert Satake relation and the archimedean identity of
  infinitesimal characters, for the standard definite group of a CM field unramified at finite places over its
  maximal real subfield, as `GlobalTheory.Published.BaseChangeIsobaricTransfer` and
  `GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup` (through `BaseChangeIsobaricN`, which quantifies an
  irreducible local subquotient $P_w$ of the induced product, and `DefiniteN`, which places its predicates on the
  induced product `locProd` itself, the two being bridged through irreducibility; the blocks are given by `CsdAsc`,
  a normalized conjugate self-dual cuspidal core with a length and an embedding relation `AscEmb`).
