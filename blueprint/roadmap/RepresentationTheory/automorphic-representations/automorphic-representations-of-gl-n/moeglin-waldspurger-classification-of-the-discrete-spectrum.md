# Mœglin–Waldspurger classification of the discrete spectrum of GLₙ

This node is still to be broken down. It covers the description of the discrete automorphic spectrum of $\mathrm{GL}_N$
that the endoscopic classification of unitary groups uses. Let $F$ be a number field and $\mathrm{GL}(N, \mathbb{A}_F)^1$ the
kernel of $\lvert \det \rvert$.

- **Theorem** (Mœglin–Waldspurger). The unitary irreducible representations of $\mathrm{GL}(N, \mathbb{A}_F)$ whose restriction to
  $\mathrm{GL}(N, \mathbb{A}_F)^1$ occurs discretely in $L^2(\mathrm{GL}(N, F) \backslash \mathrm{GL}(N, \mathbb{A}_F)^1)$ are exactly the isobaric
  sums $\mu \lvert \det \rvert^{(n-1)/2} \boxplus \mu \lvert \det \rvert^{(n-3)/2} \boxplus \dots \boxplus \mu \lvert \det \rvert^{(1-n)/2}$,
  with $N = mn$ and $\mu$ a unitary cuspidal automorphic representation of $\mathrm{GL}(m, \mathbb{A}_F)$; no two of these are
  isomorphic unless $m$, $n$ and $\mu$ agree. The cuspidal ones are those with $n = 1$, and those with $n > 1$ are
  residual, spanned by residues of Eisenstein series.

## Expansion

A good expansion has a statement page for the theorem, after a definition page for isobaric sums, citing the sources
below with locators; Mœglin and Waldspurger prove it through the residues of the Eisenstein series induced from
$\mu^{\otimes n}$ and the classification of the residual spectrum. The global normalizing factors of their intertwining
operators are built from shifted ratios of Rankin–Selberg $L$-functions of pairs of cuspidal representations and from
$\varepsilon$-factors; their poles identify the candidate residues, which survive or cancel according to the normalized local
intertwining operators, analysed separately. Already in rank one the spherical factor is a ratio whose denominator is
shifted by $1$, not a single $L$-function.

## Depends on

- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for the residual spectrum
- [Jacquet–Shalika classification of automorphic representations of GLₙ](jacquet-shalika-classification.md), for isobaric sums

## Proof depends on

- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for the residues that span the residual spectrum
- [Rankin–Selberg L-functions for GLₙ × GLₘ](rankin-selberg-l-functions-for-gl-n.md), for the $L$-functions of pairs of cuspidal representations and their poles, which normalize the intertwining operators

## Sources

- T. Kaletha, A. Mínguez, S. W. Shin and P.-J. White, "Endoscopic classification of representations: inner forms of
  unitary groups", arXiv:1409.3731: §1.3.2, (1.3.1)–(1.3.3), p. 64 (isobaric sums; Mœglin and Waldspurger identified
  $\mathcal{A}_2(N)$ with the representations (1.3.2); the chain $\mathcal{A}_{\mathrm{cusp}}(N) \subset \mathcal{A}_2(N) \subset \mathcal{A}(N)
  \subset \mathcal{A}^+_{\mathrm{iso}}(N)$).
- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §26, Theorem 26.2 (Mœglin–Waldspurger) and the paragraph after it.
- C. Mœglin and J.-L. Waldspurger, "Le spectre résiduel de GL(n)", Ann. Sci. École Norm. Sup. (4) 22 (1989), 605–674,
  the original theorem, as cited by Kaletha, Mínguez, Shin and White; p. 606 (the Rankin–Selberg $L$-functions of pairs in
  the global normalizing factors), with the normalized local intertwining operators in I.8 and I.11.
