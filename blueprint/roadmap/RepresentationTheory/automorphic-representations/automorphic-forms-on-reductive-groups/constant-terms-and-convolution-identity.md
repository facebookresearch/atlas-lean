# Constant terms and Harish-Chandra's convolution identity for automorphic forms

This node is still to be broken down. It covers basic properties of
[automorphic forms](automorphic-forms-and-automorphic-representations.md) used by the pages on
[rapid decay](rapid-decay-of-cusp-forms.md), [Harish-Chandra's finiteness theorem](harish-chandra-finiteness-theorem.md)
and [constituents of induced representations](automorphic-representations-as-constituents-of-induced-representations.md).
Let $k$, $G$, $K = K_\infty K_f$, $G_\infty$ and the centre $\mathcal{Z}$ of the enveloping algebra be as for automorphic forms.

- **Convolution identity** (Harish-Chandra). For a smooth function $\varphi$ on $G(k) \backslash G(\mathbb{A})$ that is $K$-finite
  and $\mathcal{Z}$-finite, in particular an automorphic form, and every neighbourhood $U$ of $1$ in $G_\infty$, there is a
  function $\alpha \in C^\infty_c(U)$, invariant under conjugation by $K_\infty$, with $\varphi = \varphi \star \alpha$. Consequently every automorphic
  form is of uniform moderate growth.
- **The split centre.** An automorphic form is finite under translation by the centre $Z_G(\mathbb{A})$ (Langlands's
  Lemma 3). Along the split component $A_G(\mathbb{R})^0$ of the centre, a smooth $\mathcal{Z}$-finite function satisfies
  $\varphi(xa) = \sum_i Q_i(a) (P_i \varphi)(x)$ for $a \in A_G(\mathbb{R})^0$ and $x \in G(\mathbb{A})^1$, with exponential polynomials $Q_i$ and elements $P_i$ of
  $\mathcal{Z}$ (Borel, 6.6), so that statements on $G(\mathbb{A})$ reduce to statements on $G(\mathbb{A})^1$.
- **Constant terms are automorphic forms.** For a parabolic subgroup $P = MN$ over $k$ and $g \in G(\mathbb{A})$, the
  function $m \mapsto \varphi_P(mg)$ on $M(\mathbb{A})$ obtained from the constant term of an automorphic form $\varphi$ is an automorphic
  form on $M(\mathbb{A})$: finite under a maximal compact subgroup of $M(\mathbb{A})$ containing the projection of $gKg^{-1} \cap P(\mathbb{A})$,
  with types determined by those of $\varphi$, of moderate growth, and finite under the centre of the enveloping
  algebra of $\mathfrak{m}$, through Harish-Chandra's homomorphism $\mathcal{Z}(\mathfrak{g}) \to \mathcal{Z}(\mathfrak{m})$ (Langlands's Lemma 4; Borel, 7.4 (a)–(c)).
- **Cuspidal components.** The space of cuspidal automorphic forms on $N(\mathbb{A}) M(k) \backslash G(\mathbb{A})$ is a direct sum of
  irreducible subspaces; after twisting by characters of the centre $A_M(\mathbb{A})$ of $M(\mathbb{A})$, each irreducible
  representation occurring in it can be realized by functions $\varphi$ with $\varphi(ag) = \chi(a) \varphi(g)$ for a character $\chi$ of
  $A_M(\mathbb{A})$ (Langlands's Lemma 6 and the discussion before it).

A good expansion has pages for Harish-Chandra's convolution identity and uniform moderate growth, for the
behaviour along the split centre, for the automorphy of constant terms on the Levi factors with
Harish-Chandra's homomorphism, and for the central decomposition of cuspidal forms on the Levi factors, each
with a precise statement and the locators below.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-and-automorphic-representations.md), for automorphic forms, constant terms and cusp forms
- [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for $(\mathfrak{g}, K)$-modules and the centre of the enveloping algebra

## Sources

- A. Borel, "Automorphic forms on reductive groups", lecture notes (Park City),
  <http://homepages.math.uic.edu/~rtakloo/papers/borel/borel3.pdf>: §4.2, Theorem (there is a $K$-invariant
  $\alpha \in C^\infty_c(U)$ with $f = f \star \alpha$, "by a theorem of Harish-Chandra"), §4.3, Corollary (uniform moderate growth), §6.6,
  Proposition (exponential polynomials along $A_G$) and §7.4 (a)–(c) (the constant term is an automorphic form on the
  Levi factor).
- R. P. Langlands, "On the notion of an automorphic representation", in *Automorphic forms, representations
  and L-functions*, Proc. Sympos. Pure Math. 33, Part 1, American Mathematical Society, 1979, 203–207;
  author's version <https://sunsite.ubc.ca/DigitalMathArchive/Langlands/pdf/notion-ps.pdf>: Lemma 3
  ($Z(\mathbb{A})$-finiteness), Lemma 4 (constant terms on $M(\mathbb{A})$), p. 4 and Lemma 6 (the cuspidal decomposition after a
  central twist).
