# Essentially square-integrable representations of GLₙ

Let $F$ be a non-archimedean local field, $G_n = \mathrm{GL}_n(F)$ with centre $Z_n \cong F^\times$,
$\nu = \lvert \det \rvert_F$, and use the representations $\langle \Delta \rangle^t$ of
[Zelevinsky's classification](zelevinsky-classification.md). Let $\pi$ be an irreducible
representation of $G_n$; it is admissible and has a central character $\omega_\pi$. It is
**square-integrable** if $\omega_\pi$ is unitary and its matrix coefficients $c$ satisfy
$\int_{Z_n \backslash G_n} \lvert c \rvert^2 < \infty$, and **essentially square-integrable** if its
matrix coefficients are square-integrable on $G_n^0 = \{g \in G_n \mid \lvert \det g \rvert_F = 1\}$.
Since $\pi$ has a central character, there is a unique positive character $\chi$ of $F^\times$
such that $\pi\chi$ has a unitary central character, and $\pi$ is essentially square-integrable if
and only if $\pi\chi$ is square-integrable; so for irreducible representations this is
Zelevinsky's quasi-square-integrability, square-integrability after a twist by a character. For
representations without a central character the two notions differ: the representation
$1 \oplus \nu$ of $G_1$ has bounded matrix coefficients on the compact group $G_1^0$, but no twist
of it has a unitary central character.

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
- [Cuspidal representations and Jacquet's embedding theorem](../representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for the admissibility of irreducible representations, which gives them central characters

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
  arXiv:math/0011210 (version 2): (2.3.1) and (2.3.3) (essentially $L^2$ and $L^2$
  representations, through matrix coefficients on $G^0$, respectively modulo the centre with a
  unitary central character), (2.3.6) (for representations with a central character, the unique
  positive twist with unitary central character and the equivalence with Zelevinsky's
  quasi-square-integrability; the theorem and the condition for square-integrability), (2.2.13)
  (the Steinberg representation).
- W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, notes, draft of 1 May 1995, <https://personal.math.ubc.ca/~cass/research/pdf/p-adic-book.pdf>:
  Theorem 4.4.6 (the square-integrability criterion, cited by Zelevinsky from an earlier version
  of these notes as Theorem 6.5.1).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a form of this theorem as `GlobalTheory.Published.EssSquareIntegrableSegments`.
