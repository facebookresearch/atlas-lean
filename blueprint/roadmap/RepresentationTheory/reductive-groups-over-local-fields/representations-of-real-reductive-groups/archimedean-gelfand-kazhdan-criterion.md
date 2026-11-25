# Archimedean Gelfand–Kazhdan criterion

This node is still to be broken down. It covers the criterion of Gelfand and Kazhdan type, in the general form of
Sun and Zhu, that the page on archimedean Whittaker models uses. Let $G$ be a real reductive group in the sense of Sun
and Zhu: its Lie algebra is reductive, it has finitely many connected components, and the connected subgroup with Lie
algebra $[\mathfrak{g}, \mathfrak{g}]$ has finite centre; the group of real points of a reductive algebraic group is an
example. Let $S_1, S_2$ be closed subgroups with continuous characters $\chi_i \colon S_i \to \mathbb{C}^\times$, and $\sigma$ a
continuous anti-automorphism of $G$, written $x \mapsto x^\sigma$.

- **Tempered generalized functions.** A smooth function $f$ on $G$ is Schwartz if $\sup_x \phi(x) \lvert (Xf)(x) \rvert$ is
  finite for every $X$ in the enveloping algebra of $\mathfrak{g}_{\mathbb{C}}$ and every positive function $\phi$ of moderate
  growth. The Schwartz densities $f \, dg$ form a nuclear Fréchet space, and a tempered generalized function on $G$ is a
  continuous linear functional on it. A smooth function all of whose derivatives have moderate growth is one.
- **Generalized matrix coefficients** (Sun–Zhu, Theorem 2.1). For contragredient Casselman–Wallach representations
  $U^\infty$ and $V^\infty$ of $G$, let $V^{-\infty}$ and $U^{-\infty}$ be the strong duals of $U^\infty$ and $V^\infty$. The matrix
  coefficient map $(u, v) \mapsto (g \mapsto \langle gu, v \rangle)$ extends to a continuous bilinear map from
  $U^{-\infty} \times V^{-\infty}$ to the tempered generalized functions, and the induced map on the completed projective tensor
  product is a topological homomorphism with closed image.
- **Theorem** (Sun–Zhu, Theorem 2.3 (a)). Suppose that every tempered generalized function $f$ on $G$ that is an
  eigenvector of the bi-invariant differential operators and satisfies $f(sx) = \chi_1(s) f(x)$ for $s \in S_1$ and
  $f(xs) = \chi_2(s)^{-1} f(x)$ for $s \in S_2$ also satisfies $f(x^\sigma) = f(x)$. Then for every pair of contragredient
  irreducible Casselman–Wallach representations $U^\infty$ and $V^\infty$ of $G$,
  $\dim \mathrm{Hom}_{S_1}(U^\infty, \mathbb{C}_{\chi_1}) \cdot \dim \mathrm{Hom}_{S_2}(V^\infty, \mathbb{C}_{\chi_2}) \le 1$, the
  homomorphisms being continuous. The inverse on $\chi_2$ matters: for $G = \mathrm{U}(2)$, both $S_i$ its centre,
  $\chi_1(z) = z$ and $\chi_2(z) = z^{-1}$, the law $f(xs) = \chi_2(s) f(x)$ would admit only $f = 0$, while for the standard
  representation and its dual both spaces of homomorphisms have dimension $2$.

## Expansion

A good expansion has definition pages for Schwartz functions and densities and for tempered generalized functions, and
statement pages for the generalized matrix coefficients and for the theorem with Sun and Zhu's hypotheses and their
Remark 2.4, each citing the source below with locators. Sun and Zhu prove Theorem 2.1 in their §3, pp. 7–11, from the
Casselman–Wallach globalization, polynomially controlled integration of Schwartz functions, the completed projective
tensor product of nuclear Fréchet spaces and its strong dual, and a lemma on transposes with closed image (Lemma 3.8,
p. 11). They prove Theorem 2.3 in §4, pp. 11–13, by applying the hypothesis to the generalized matrix coefficient of two
nonzero $S_i$-equivariant functionals, with Lemma 3.7, Lemma 4.1 and Schur's lemma; when either space of functionals is
zero the bound is immediate. These are steps of the node's own proof.

## Depends on

- [Casselman–Wallach globalization theorem](casselman-wallach-globalization.md), for Casselman–Wallach representations
- [Vector-valued integrals and distributions on Lie groups](../../lie-and-topological-representations/vector-valued-integrals-and-distributions-on-lie-groups.md), for distributions on Lie groups, to which tempered generalized functions restrict

## Proof depends on

- [Casselman–Wallach globalization](casselman-wallach-globalization.md), for the exact globalization functor and the closed range of the maps between globalizations that Sun and Zhu's proof of their Theorem 2.1 uses; the polynomially controlled Schwartz integration, the nuclear Fréchet tensor products with their strong duals and the transpose lemma are steps of the node's own proof, as the Expansion describes

## Sources

- B. Sun and C.-B. Zhu, "A general form of Gelfand–Kazhdan criterion", arXiv:0903.1409 (version 6): §1, pp. 1–4 (real
  reductive groups, moderate growth, Schwartz functions and densities, tempered generalized functions and
  Casselman–Wallach representations), Theorem 2.1, pp. 4–5 (generalized matrix coefficients), Theorem 2.3 (a), pp. 5–6,
  Remark 2.4, §3, pp. 7–11 (proof of Theorem 2.1), and §4, pp. 11–13 (proof of Theorem 2.3).
