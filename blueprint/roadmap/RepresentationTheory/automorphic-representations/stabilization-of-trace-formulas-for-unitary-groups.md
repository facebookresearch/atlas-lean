# Stabilization of the trace formulas for unitary groups and their twisted comparison group

This node is still to be broken down. It covers the stabilizations of the discrete parts of the trace formulas, with the
fundamental lemmas and the transfer behind them, on which the endoscopic classification of unitary groups rests. Let
$E/F$ be a quadratic extension of number fields, $U_{E/F}(N)$ the quasi-split unitary group, $\tilde G_{E/F}(N)$ the twisted
group attached to the restriction of scalars of $\mathrm{GL}_N$ from $E$ to $F$ and its outer automorphism, and $(G, \xi)$
an inner twist of $U_{E/F}(N)$. For $G$ one of these groups, $I^G_{\mathrm{disc}, t}$ is the discrete part of its trace formula,
a linear form on test functions $f$ built from [automorphic representations](automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md).

- **Stabilization.** $I^G_{\mathrm{disc}, t}(f) = \sum_{G'} \iota(G, G') \hat S^{G'}_{\mathrm{disc}, t}(f^{G'})$, the sum over the elliptic
  endoscopic data $G'$ of $G$, with $f^{G'}$ the Langlands–Kottwitz–Shelstad transfer of $f$ and $\hat S^{G'}_{\mathrm{disc}, t}$ stable
  linear forms.
- **For connected groups.** For $U_{E/F}(N)$ this is Arthur's stabilization, which rests on the transfer and on the standard
  and weighted fundamental lemmas (Waldspurger, Ngô, Chaudouard–Laumon; for unitary groups the standard fundamental
  lemma is due to Laumon and Ngô). For the inner twists $(G, \xi)$ it also needs the weighted fundamental lemma in
  general.
- **For the twisted group.** The stabilization for $\tilde G_{E/F}(N)$, with the twisted transfer and fundamental lemmas
  (Waldspurger, Ngô), is Mok's Hypothesis 4.2.1; when Mok and Kaletha, Mínguez, Shin and White wrote, it was the
  work in progress of Waldspurger, in part with Mœglin.

## Expansion

A good expansion has statement pages for the stabilization of each of the three trace formulas, recording for each
the fundamental lemmas and transfer statements it uses, and the published proofs that remove the hypotheses, citing
the sources below with locators.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for automorphic representations and the discrete spectrum

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- C. P. Mok, "Endoscopic classification of representations of quasi-split unitary groups", Mem. Amer. Math. Soc. 235
  (2015), no. 1108, arXiv:1206.0882 (version 5): §2.6, p. 38 (the results are conditional on the stabilization of the
  twisted trace formula), and §4.2, pp. 87–88 (the stabilization for connected groups, after Arthur, Waldspurger, Ngô,
  Chaudouard–Laumon and Laumon–Ngô; the decomposition (4.2.1); Hypothesis 4.2.1 for the twisted group).
- T. Kaletha, A. Mínguez, S. W. Shin and P.-J. White, "Endoscopic classification of representations: inner forms of
  unitary groups", arXiv:1409.3731: Introduction, p. 6 (the main results of Mok are taken as given; the weighted
  fundamental lemma in general is needed for the stabilization of the untwisted trace formula for inner forms).
