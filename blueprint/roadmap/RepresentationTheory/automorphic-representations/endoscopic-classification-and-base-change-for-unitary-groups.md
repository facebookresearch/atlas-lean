# Endoscopic classification and base change for unitary groups

This node is still to be broken down. It covers the classification of the discrete automorphic spectrum of
unitary groups in terms of automorphic representations of general linear groups, and the base change
from unitary groups to $\mathrm{GL}_N$ that it gives. Let $E/F$ be a quadratic extension of number fields
and $U_{E/F}(N)$ the quasi-split unitary group in $N$ variables.

- **Global parameters.** Formal square-integrable parameters
  $\psi = \mu_1 \boxtimes \nu_1 \boxplus \dots \boxplus \mu_r \boxtimes \nu_r$ with distinct pairs $(\mu_i, \nu_i)$,
  $\mu_i$ a conjugate self-dual unitary
  [cuspidal automorphic representation](automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md)
  of $\mathrm{GL}_{m_i}(\mathbb{A}_E)$, $\nu_i$ the irreducible representation of $\mathrm{SL}_2(\mathbb{C})$ of dimension
  $d_i$, $\sum_i m_i d_i = N$, each $\mu_i \boxtimes \nu_i$ satisfying a parity condition relative to $N$.
- **Classification** (Mok). For the quasi-split group, the discrete spectrum
  $L^2_{\mathrm{disc}}(U_{E/F}(N)(F) \backslash U_{E/F}(N)(\mathbb{A}_F))$ decomposes as the direct sum over
  square-integrable parameters $\psi$ of the representations in the subsets $\Pi_\psi(\varepsilon_\psi)$ of the
  global packets cut out by the sign character $\varepsilon_\psi$; the proof rests on the stabilization of the
  twisted trace formula.
- **Weak base change** (Mok). Every discrete automorphic representation of $U_{E/F}(N)$ has a weak base
  change to an automorphic representation of $\mathrm{GL}_N(\mathbb{A}_E)$ with matching Satake parameters at
  almost all places, with respect to an $L$-embedding $\xi$.
- **Inner forms** (Kaletha–Mínguez–Shin–White). The same decomposition for inner twists of
  $U_{E/F}(N)$, among them the unitary groups of definite Hermitian spaces over CM extensions, proved there
  under hypotheses resolved in sequels, and unconditionally for generic parameters and pure inner twists.
  For a definite unitary group, the parameter of a discrete automorphic representation gives its base
  change, an isobaric automorphic representation of $\mathrm{GL}_N(\mathbb{A}_E)$.

A good expansion has pages for the global parameters and their localizations, the local and global
packets and the sign character, the classification for quasi-split unitary groups, the weak base change,
and the classification and base change for inner forms, with the conditional status of each statement
recorded; the base change for definite unitary groups should also be checked against J.-P. Labesse,
"Changement de base CM et séries discrètes", in *On the Stabilization of the Trace Formula*, International
Press, 2011, with locators.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for automorphic and cuspidal automorphic representations
- [Jacquet–Shalika classification of automorphic representations of GLₙ](automorphic-representations-of-gl-n/jacquet-shalika-classification.md), for isobaric sums of cuspidal representations of general linear groups
- [Discreteness of the cuspidal spectrum](automorphic-forms-on-reductive-groups/discreteness-of-the-cuspidal-spectrum.md), for discrete spectra

## Sources

- C. P. Mok, "Endoscopic classification of representations of quasi-split unitary groups", Mem.
  Amer. Math. Soc. 235 (2015), no. 1108, arXiv:1206.0882 (version 5): introduction, §2.3 (formal global
  parameters $\mu \boxtimes \nu$), Definition 2.4.7 (square-integrable parameters and their parity
  condition), Theorem 2.5.2 (decomposition of the discrete spectrum), §2.6 (the stabilization of the twisted
  trace formula), §4.3 with display (4.3.5), Corollary 4.3.8 and the paragraph after it ("corollary 4.3.8
  gives in particular the existence of 'weak base change' associated to discrete automorphic
  representations on $U_{E/F}(N)$ (with respect to the L-embedding $\xi$)").
- T. Kaletha, A. Mínguez, S. W. Shin and P.-J. White, "Endoscopic classification of representations: inner
  forms of unitary groups", arXiv:1409.3731: Theorem* 1.7.1 (the decomposition for inner twists of
  $U_{E/F}(N)$) and the paragraph after it (proved under two hypotheses resolved in sequels; unconditional for
  generic parameters and pure inner twists).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states base change for definite unitary groups over CM fields as
  `GlobalTheory.Published.BaseChangeIsobaricTransfer` and
  `GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup`.
