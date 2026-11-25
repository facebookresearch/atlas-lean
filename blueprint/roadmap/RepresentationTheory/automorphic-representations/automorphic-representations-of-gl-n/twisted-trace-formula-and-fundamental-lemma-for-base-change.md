# The twisted trace formula and the fundamental lemma for cyclic base change of GLₙ

This node is still to be broken down. It covers the external inputs of the Arthur–Clozel comparison of trace formulas
for cyclic base change. Let $E/F$ be a cyclic extension of number fields of prime degree $\ell$, $\sigma$ a generator of its
Galois group, $G^0 = \mathrm{R}_{E/F}\mathrm{GL}_n$, $\theta$ the automorphism of $G^0$ defined by $\sigma$, and $G = G^0 \rtimes \theta$, a
connected component of a non-connected reductive group over $F$; let $G' = \mathrm{GL}_n$ over $F$.

- **Invariant twisted trace formula** (Arthur). For a connected component $G$ of a reductive group over a number field with
  $G(F)$ nonempty, the invariant trace formula holds for distributions on $G(\mathbb{A})$ invariant under conjugation by the
  identity component, under one condition: the twisted form of the archimedean trace Paley–Wiener theorem of Clozel
  and Delorme holds for $G$, the $p$-adic form being due to Rogawski. For the base change group above the condition holds:
  at the finite places it is Rogawski's twisted Paley–Wiener theorem, at the archimedean places where $E$ splits it
  reduces to the untwisted theorem, and in the remaining case, $\mathbb{C}/\mathbb{R}$, Arthur and Clozel prove it.
- **Fundamental lemma for unit elements** (Kottwitz). At almost all places $v$, namely the finite places where $E/F$ is
  unramified, the characteristic function of
  $G(\mathcal{O}_v)$ in $G(F_v)$ and that of $\mathrm{GL}_n(\mathcal{O}_v)$ in $G'(F_v)$ correspond under the transfer of twisted orbital
  integrals along the norm map from $G$ to $G'$.

## Expansion

A good expansion has definition pages for twisted orbital integrals, the norm map and the twisted trace formula, and
statement pages for the invariant twisted trace formula with its Paley–Wiener condition, for its verification in the
base change case, and for Kottwitz's fundamental lemma, each citing the sources below with locators.
The density argument at the top of p. 196 of Arthur and Clozel has a gap that Arthur fills in "A stable trace formula
III", Lemma 8.2; a statement page for that lemma, after reading it, belongs beside these.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for automorphic representations; non-connected groups, twisted orbital integrals, the norm map and the twisted trace formula are the node's own definitions, as the Expansion says
- [Adelic points of reductive groups: the norm-one subgroup and maximal compact subgroups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/adelic-points-of-reductive-groups.md), for the adelic points of $G^0$ and $G'$ and the maximal compact subgroups $G^0(\mathcal{O}_v)$ at almost all places
- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for the test functions at the archimedean places, the smooth compactly supported functions on $G(F_v)$ that are $K$-finite under left and right translation (Arthur and Clozel, Chapter 1, §7), acting through the integrated action; they are functions on the whole group, not the $K$-supported distributions of the $(\mathfrak{g}, K)$ Hecke algebra
- [Hecke-algebra corners of smooth representations and independence of their characters](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/hecke-algebra-corners-and-character-independence.md), for the Hecke algebras of test functions at the finite places
- [Cartan decomposition and Satake isomorphism for special maximal compact subgroups](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/cartan-decomposition-and-satake-isomorphism.md), for the spherical Hecke algebras and their units, the characteristic functions of $G(\mathcal{O}_v)$ and $\mathrm{GL}_n(\mathcal{O}_v)$

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and Shimura Varieties*,
  Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §26, pp. 189–191 (the invariant twisted trace formula under
  the twisted trace Paley–Wiener condition of Clozel and Delorme [CD], established by Rogawski [Ro2] in the $p$-adic case;
  the fundamental lemma for unit elements, "established in the case at hand by Kottwitz [Ko4]"; the gap at p. 196 of
  [AC], "filled in [A29, Lemma 8.2]").
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*, Annals of
  Mathematics Studies 120, Princeton University Press, 1989: Chapter 1, §2, Proposition 2.9, pp. 17–18 (Rogawski's twisted
  Paley–Wiener theorem at the $p$-adic places, from his preprint [33(c)]), §4, Proposition 4.9, p. 42 (the identity for the
  units of the Hecke algebras, Kottwitz's [29(c), Lemma 8.8]), and §7, p. 71 ("the only interesting case is the extension
  $\mathbb{C}/\mathbb{R}$") and Proposition 7.1, p. 72 (the twisted trace Paley–Wiener theorem for $\mathbb{C}/\mathbb{R}$).
- R. E. Kottwitz, "Base change for unit elements of Hecke algebras", Compositio Math. 60 (1986), 237–250; L. Clozel and
  P. Delorme, "Le théorème de Paley–Wiener invariant pour les groupes de Lie réductifs II", Ann. Sci. École Norm. Sup.
  (4) 23 (1990), 193–228; and J. Arthur, "A stable trace formula III. Proof of the main theorems", Ann. of Math. 158
  (2003), 769–873, as cited by Arthur.
