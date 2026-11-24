# Harish-Chandra's convolution identity and uniform moderate growth

This node is still to be broken down. It covers Harish-Chandra's theorem that $K$-finite and
$\mathcal{Z}$-finite functions are reproduced by convolution, and its consequence for moderate growth,
which the definition of the action of the Hecke algebra on automorphic forms and the page on
[constant terms](constant-terms-and-convolution-identity.md) use. Let $k$ be a number field, $G$ a
connected reductive group over $k$, $G_\infty = \prod_{v \mid \infty} G(k_v)$, $K = K_\infty K_f$ a maximal
compact subgroup of $G(\mathbb{A})$, $\mathcal{Z}$ the centre of the enveloping algebra of the complexified
Lie algebra of $G_\infty$, and $\lVert \cdot \rVert$ a two-sided height on $G(\mathbb{A})$.

- **Convolution identity** (Harish-Chandra). For a smooth function $\varphi$ on $G(k) \backslash G(\mathbb{A})$
  that is $K$-finite and $\mathcal{Z}$-finite, and every neighbourhood $U$ of $1$ in $G_\infty$, there is a
  function $\alpha \in C^\infty_c(U)$, invariant under conjugation by $K_\infty$, with
  $\varphi = \varphi \star \alpha$.
- **Uniform moderate growth.** If such a $\varphi$ moreover has moderate growth,
  $\lvert \varphi(g) \rvert \le C \lVert g \rVert^N$, then there is one $N$ such that every derivative $D\varphi$,
  $D$ in the enveloping algebra, satisfies $\lvert D\varphi(g) \rvert \le C_D \lVert g \rVert^N$: indeed
  $D(\varphi \star \alpha) = \varphi \star D\alpha$, and convolution with a compactly supported function
  preserves moderate growth with the same exponent, because $\lVert gh \rVert$ and $\lVert g \rVert$ are
  comparable for $h$ in a compact set.

A good expansion has a page for Harish-Chandra's theorem, with its hypotheses (the elliptic element of
$\mathcal{Z} \cdot \mathcal{U}(\mathfrak{k})$ annihilating $\varphi$), and one for uniform moderate growth, citing
the sources below with locators.

## Depends on

- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the two-sided height and moderate growth
- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for $K$-finite functions
- Not yet a page: the enveloping algebra of the complexified Lie algebra of $G_\infty$ and its centre, acting on smooth functions by derivatives, for $\mathcal{Z}$-finiteness

## Proof depends on

- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for $\lVert xy \rVert \le c \lVert x \rVert \lVert y \rVert$, which makes convolution with a compactly supported function preserve moderate growth
- Not yet a page: Harish-Chandra's theorem on $\mathcal{Z}$-finite and $K$-finite functions (Harish-Chandra, Acta Math. 116 (1966), Theorem 1, as cited by Borel), for the convolution identity

## Sources

- A. Borel, "Automorphic forms on reductive groups", lecture notes (Park City),
  <http://homepages.math.uic.edu/~rtakloo/papers/borel/borel3.pdf>: §4.2, Theorem, p. 4 ("there exists a
  K-invariant function $\alpha \in C_c^\infty(U)$ such that $f = f \star \alpha$ ... by a theorem of
  Harish-Chandra. See ([12], theorem 1)"), and §4.3, Corollary, p. 4 ("if f has moderate growth, then
  $f \star \alpha$ is of uniform moderate growth").
- Harish-Chandra, "Discrete series for semisimple groups. II. Explicit determination of the
  characters", Acta Math. 116 (1966), 1–111, Theorem 1, cited by Borel as [12].
