# Stabilization of the trace formulas for unitary groups and their twisted comparison group

This node is still to be broken down. It covers the stabilizations of the discrete parts of the trace formulas, with the
fundamental lemmas and the transfer behind them, on which the endoscopic classification of unitary groups rests. Let
$E/F$ be a quadratic extension of number fields, $U_{E/F}(N)$ the quasi-split unitary group, $\tilde G_{E/F}(N)$ the twisted
group attached to the restriction of scalars of $\mathrm{GL}_N$ from $E$ to $F$ and its outer automorphism, and $(G, \xi)$
an inner twist of $U_{E/F}(N)$. For $G$ one of these groups, with a central character datum $(X_G, \omega)$, and $t \ge 0$,
$I^G_{\mathrm{disc}, t}$ is the $t$-part of the discrete part of its trace formula: the linear form on the Hecke algebra $\mathcal{H}(G, \omega)$
of test functions $f$ given by the sum, over Levi subgroups $M$ and regular elements $w$ of the relative Weyl group, of the
weighted traces of $M_{P,t}(w, \omega) I_{P,t}(\omega, f)$, where $I_{P,t}(\omega)$ is the summand of the parabolic induction of the discrete
spectrum of $M$ whose irreducible constituents $\pi$, [automorphic representations](automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md),
have archimedean infinitesimal characters $\mu_\pi$ with $\lVert \operatorname{Im} \mu_\pi \rVert = t$, and $M_{P,t}(w, \omega)$ the intertwining operator
(KMSW, (3.1.1); for the twisted group, its twisted analogue).

- **Stabilization.** $I^G_{\mathrm{disc}, t}(f) = \sum_{G'} \iota(G, G') \hat S^{G'}_{\mathrm{disc}, t}(f^{G'})$, the sum over the elliptic
  endoscopic data $G'$ of $G$, finite for each $f$, with $f^{G'}$ the Langlands–Kottwitz–Shelstad transfer of $f$ and
  $\hat S^{G'}_{\mathrm{disc}, t}$ stable linear forms depending only on $G'$. For quasi-split $G$ the identity defines $\hat S^G_{\mathrm{disc}, t}$ and
  asserts that it is stable; for the inner twists the two sides are defined independently and the identity asserts that
  they agree.
- **For connected groups: established, as these sources cite it.** For $U_{E/F}(N)$ this is Arthur's stabilization, which rests
  on the transfer and on the standard and weighted fundamental lemmas (Waldspurger, Ngô, Chaudouard–Laumon; for unitary
  groups the standard fundamental lemma is due to Laumon and Ngô). For the inner twists $(G, \xi)$ it also needs the weighted
  fundamental lemma in general. Mok and Kaletha, Mínguez, Shin and White accept it without proof.
- **For the twisted group: assumed in these sources.** The stabilization for $\tilde G_{E/F}(N)$, with the twisted transfer and
  fundamental lemmas (Waldspurger, Ngô), is Mok's Hypothesis 4.2.1, which he assumes for the rest of his paper, and on
  which the results of Kaletha, Mínguez, Shin and White depend through his; when they wrote it was the work in progress
  of Waldspurger, in part with Mœglin.

## Expansion

A good expansion has definition pages for the discrete part of the trace formula and its $t$-parts, for elliptic endoscopic
data and for transfer, and statement pages for the stabilization of each of the three trace formulas, recording for each
the fundamental lemmas and transfer statements it uses, whether the sources below prove, cite or assume it, and the
published proofs that remove the hypotheses, citing the sources with locators.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for automorphic representations; the discrete part of the trace formula, its $t$-parts, endoscopic data and transfer are the node's own definitions, after KMSW §3.1, as the Expansion says

## Proof depends on

Its proof is not given in the sources below: they cite the stabilization for the connected groups and assume it for the
twisted group, as the statement says. The Expansion records the published proofs that a statement page cites.

## Sources

- C. P. Mok, "Endoscopic classification of representations of quasi-split unitary groups", Mem. Amer. Math. Soc. 235
  (2015), no. 1108, arXiv:1206.0882 (version 5): §2.6, p. 38 (the results are conditional on the stabilization of the
  twisted trace formula), and §4.2, pp. 87–90 (the stabilization for connected groups, after Arthur, Waldspurger, Ngô,
  Chaudouard–Laumon and Laumon–Ngô; the decomposition (4.2.1), p. 88; Hypothesis 4.2.1, p. 90, assumed for the rest of
  the paper).
- T. Kaletha, A. Mínguez, S. W. Shin and P.-J. White, "Endoscopic classification of representations: inner forms of
  unitary groups", arXiv:1409.3731: Introduction, p. 6 (the main results of Mok are taken as given; the weighted
  fundamental lemma in general is needed for the stabilization of the untwisted trace formula for inner forms), and
  §3.1, pp. 142–144 (the $t$-parts and the discrete part (3.1.1), and the stabilization (3.1.3), with (3.1.4) for
  quasi-split groups, accepted from Arthur).
