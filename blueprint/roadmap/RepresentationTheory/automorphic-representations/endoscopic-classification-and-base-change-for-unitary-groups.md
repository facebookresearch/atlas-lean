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
  $\sum_i m_i d_i = N$, and every block of the same sign $\kappa_i(-1)^{N_i - 1} = \kappa(-1)^{N-1}$ (Mok's
  Definition 2.4.7, with $N_i = m_i d_i$). Each $\psi$ has a global packet and a sign character $\varepsilon_\psi$.
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
- **Base change of definite unitary groups with all local components** (pending). For a CM extension
  $E/F$ unramified at every finite place over $F$ and the unitary group of a definite Hermitian space, the
  base change of a discrete automorphic representation, as an isobaric sum of conjugate self-dual cuspidal
  representations, with: the identification of the local components at every place (at the split places
  through $\mathrm{U}(V)(F_v) \cong \mathrm{GL}_N(F_v)$, at the unramified inert places through the unramified base change
  of Satake parameters) and the identity between the archimedean weights and the infinitesimal
  characters of the base change. This is stronger than weak base change, which only matches almost all
  places; it needs the local classification at every place and should be sourced with locators, for
  instance from Labesse's work on base change for definite unitary groups or from the local–global
  compatibility in the endoscopic classification, before it is relied upon.

A good expansion has pages for the global parameters and their localizations, the local and global
packets and the sign character, the classification for quasi-split unitary groups, the weak base change,
and the classification and base change for inner forms, with the conditional status of each statement
recorded; the base change for definite unitary groups should also be checked against J.-P. Labesse,
"Changement de base CM et séries discrètes", in *On the Stabilization of the Trace Formula*, International
Press, 2011, with locators.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for automorphic and cuspidal automorphic representations
- [Jacquet–Shalika classification of automorphic representations of GLₙ](automorphic-representations-of-gl-n/jacquet-shalika-classification.md), for isobaric sums of cuspidal representations of general linear groups
- [Discreteness of the cuspidal spectrum](automorphic-forms-on-reductive-groups/discreteness-of-the-cuspidal-spectrum.md), for the cuspidal part of the discrete spectrum (the residual part is described through Eisenstein series)
- [Eisenstein series and their meromorphic continuation](automorphic-forms-on-reductive-groups/eisenstein-series.md), for the residual spectrum

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
  forms of unitary groups", arXiv:1409.3731: Theorem* 1.7.1 (the decomposition for inner twists of
  $U_{E/F}(N)$) and the paragraph after it (proved in Chapter 5 under two hypotheses, whose resolution is
  announced for the sequels [KMSa], [KMSb]; unconditional for generic parameters and pure inner twists).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the base change of the pending item, for CM extensions unramified at every finite place over
  their maximal real subfield, $N \ge 1$ and the standard definite group, with its local compatibilities at
  every place and its archimedean weight identity, as `GlobalTheory.Published.BaseChangeIsobaricTransfer` and
  `GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup`.
