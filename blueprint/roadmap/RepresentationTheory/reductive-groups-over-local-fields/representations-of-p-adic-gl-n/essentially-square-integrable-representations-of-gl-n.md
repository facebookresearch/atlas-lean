# Essentially square-integrable representations of GLₙ

Let $F$ be a non-archimedean local field, $G_n = \mathrm{GL}_n(F)$ with centre $Z_n \cong F^\times$,
$\nu = \lvert \det \rvert_F$, and use the representations $\langle \Delta \rangle^t$ of
[Zelevinsky's classification](zelevinsky-classification.md). An admissible representation $\pi$
of $G_n$ is **essentially square-integrable** (quasi-square-integrable) if, after multiplying by a
suitable character of $G_n$, all its matrix coefficients become square-integrable on $G_n$ modulo
$Z_n$; it is **square-integrable** if it has a unitary central character and its matrix
coefficients $c$ satisfy $\int_{Z_n \backslash G_n} \lvert c \rvert^2 < \infty$.

**Theorem (Bernstein).** An irreducible representation of $G_n$ is essentially square-integrable
if and only if it is isomorphic to $\langle \Delta \rangle^t$ for some segment $\Delta$. It is
square-integrable if and only if moreover $\Delta = [\rho, \nu^{m-1}\rho]$ with
$\nu^{(m-1)/2}\rho$ of unitary central character.

For instance, for the segment $\Delta = [\nu^{-(n-1)/2}, \nu^{(n-1)/2}]$ of characters of $G_1$,
$\langle \Delta \rangle$ is the trivial representation of $G_n$ and $\langle \Delta \rangle^t$ is
the Steinberg representation.

## Depends on

- [Zelevinsky's classification of the irreducible representations of GLₙ](zelevinsky-classification.md), for segments and the representations $\langle \Delta \rangle^t$
- [Smooth and admissible representations of p-adic groups](../representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for matrix coefficients, characters and central characters

## Proof depends on

- [Jacquet modules and the asymptotics of matrix coefficients](../representations-of-p-adic-reductive-groups/asymptotics-of-matrix-coefficients.md), for Casselman's square-integrability criterion in terms of the exponents of Jacquet modules
- [Zelevinsky's classification of the irreducible representations of GLₙ](zelevinsky-classification.md), for the Jacquet modules of $\langle \Delta \rangle^t$ and the classification

## Sources

- A. V. Zelevinsky, "Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)", Ann. Sci. École Norm. Sup. (4) 13 (1980), 165–210,
  <http://www.numdam.org/item?id=ASENS_1980_4_13_2_165_0>: §9.1 (the Jacquet module property
  (*) of $\langle \Delta \rangle^t$), Example 9.2 (the Steinberg representation) and Theorem 9.3
  (Bernstein): the representations $\langle \Delta \rangle^t$ are quasi-square-integrable by
  Casselman's criterion; "The converse is due to Bernstein and is based on a refinement of results
  of Casselman. The proof is omitted."
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): (2.3.1) and (2.3.3) (essentially square-integrable and
  square-integrable representations), (2.3.6) (the equivalence with quasi-square-integrability,
  the theorem, and the condition for square-integrability), (2.2.13) (the Steinberg
  representation).
- W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, notes, draft of 1 May 1995, <https://personal.math.ubc.ca/~cass/research/pdf/p-adic-book.pdf>:
  Theorem 4.4.6 (the square-integrability criterion, cited by Zelevinsky from an earlier version
  of these notes as Theorem 6.5.1).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a form of this theorem as `GlobalTheory.Published.EssSquareIntegrableSegments`.
