# Square-integrable K-finite and Z-finite functions are automorphic forms

This node is still to be broken down. It covers the regularity of square-integrable functions on arithmetic quotients that
are finite under $K$ and under the centre of the enveloping algebra, which the decomposition of the cuspidal spectrum uses.
Let $G$ be the real points of a reductive group, $\Gamma$ an arithmetic subgroup with $\Gamma \backslash G$ of finite volume,
$K$ a maximal compact subgroup and $\mathcal{Z}$ the centre of the enveloping algebra. For a reductive group over a number
field $k$ and a fixed compact open subgroup $L$ of its finite adelic points, $G(k) \backslash G(\mathbb{A})^1 / L$ is a finite union
of quotients $\Gamma_i \backslash G_\infty^1$ of this kind, so the statements below also hold for functions on
$G(k) \backslash G(\mathbb{A})^1$ invariant under $L$.

- **Regularity.** Let $f$ be a class in $L^p(\Gamma \backslash G)$ for some $p \ge 1$ that is $K$-finite and is annihilated, in the
  sense of distributions, by an ideal of finite codimension of $\mathcal{Z}$. Then $f$ has a unique representative that is
  smooth and of moderate growth, and this representative is an
  [automorphic form](automorphic-forms-and-automorphic-representations.md). Other representatives need not be smooth, since a
  class does not see the values of a function on a null set.
- **Discrete spectrum.** In particular every $K$-finite, $\mathcal{Z}$-finite class in $L^2(\Gamma \backslash G)$ has a unique
  smooth representative of moderate growth, which is an automorphic form.

## Expansion

A good expansion has statement pages for the regularity and for its consequence for $L^2$, each citing the source below with
locators. Borel first shows that $f$ is annihilated by a nonconstant polynomial in the elliptic operator
$\Omega = 2 C_{\mathfrak{k}} + C_{\mathfrak{g}}$, which elliptic regularity turns into the real analyticity of a representative.
Only then does he apply Harish-Chandra's convolution identity $f = f \star \alpha$ to that smooth representative, and he
obtains its moderate growth from the $L^p$ bound, the convolution and the counting estimate
$\#(\Gamma \cap G_t) \ll t^m$ for the elements of norm at most $t$.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-and-automorphic-representations.md), for automorphic forms
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the finite volume of the quotients and the finitely many arithmetic quotients $\Gamma_i \backslash G_\infty^1$ at a fixed level $L$

## Proof depends on

- [Analytic elliptic regularity](../../../Analysis/partial-differential-equations/analytic-elliptic-regularity.md), for the real analyticity of a class annihilated by a nonconstant polynomial in the elliptic operator $\Omega$
- [Harish-Chandra's convolution identity and uniform moderate growth](harish-chandra-convolution-identity.md), for the convolution identity applied to the smooth representative, which gives its moderate growth together with the $L^p$ bound
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the polynomial bound on the number of elements of bounded height, the counting estimate in Borel's Lemma 4.5

## Sources

- A. Borel, "Automorphic forms on reductive groups", lecture notes (Park City),
  <http://homepages.math.uic.edu/~rtakloo/papers/borel/borel3.pdf>: §3.1, p. 2 ((A1)–(A4), with $\mathcal{Z}$-finiteness in the
  sense of distributions for a function that is not smooth), §4.1, p. 4 (analyticity, by a regularity theorem, from an
  annihilating polynomial in $\Omega$), §4.2 (the convolution identity, after Harish-Chandra), §4.4 and Lemma 4.5, pp. 5–6 (the
  counting estimates and the bound for $u \star \alpha$), Proposition 4.1, p. 6 (on a finite-volume quotient, a function satisfying
  (A1)–(A3) that lies in some $L^p$ has moderate growth, hence is an automorphic form), and "Discrete spectrum
  and L²-automorphic forms", pp. 27–28 (the $K$-finite, $\mathcal{Z}(\mathfrak{g})$-finite elements of $L^2(\Gamma \backslash G)$ are
  automorphic forms).
