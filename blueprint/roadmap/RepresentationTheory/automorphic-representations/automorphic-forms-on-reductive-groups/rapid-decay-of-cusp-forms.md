# Rapid decay of cusp forms

Let $k$, $G$, $K$, $\mathfrak{g}$ and the height $\lVert \cdot \rVert$ be as for
[automorphic forms](automorphic-forms-and-automorphic-representations.md), let
$G(\mathbb{A})^1 = \{x \in G(\mathbb{A}) : H_G(x) = 0\}$, and let $\mathfrak{S}$ range over the
[Siegel sets](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md) of $G(\mathbb{A})$, with
$\mathfrak{S}^1 = \mathfrak{S} \cap G(\mathbb{A})^1$. A smooth function $\varphi$ on
$G(k) \backslash G(\mathbb{A})^1$ is uniformly of moderate growth if there is $N_0$ such that for every left
invariant differential operator $X$ on $G(\mathbb{R})^1$ there is $c_X$ with
$\lvert (X\varphi)(x) \rvert \le c_X \lVert x \rVert^{N_0}$ for all $x$, and it is rapidly decreasing if for
every $N$ and every Siegel set $\mathfrak{S}$ there is $C$ with $\lvert \varphi(x) \rvert \le C \lVert x \rVert^{-N}$
on $\mathfrak{S}^1$.

1. **Uniform moderate growth** (Harish-Chandra). Every automorphic form is uniformly of moderate
   growth.
2. **Rapid decay** (Gelfand–Piatetski-Shapiro; Harish-Chandra). A smooth function on
   $G(k) \backslash G(\mathbb{A})^1$ that is right invariant under an open compact subgroup of $G(\mathbb{A}_f)$,
   uniformly of moderate growth and cuspidal (all its constant terms along proper parabolic subgroups over
   $k$ vanish) is rapidly decreasing. In particular cusp forms are rapidly decreasing on
   $G(\mathbb{A})^1$, bounded there, and square integrable on $G(k) \backslash G(\mathbb{A})^1$.
3. **$\mathrm{GL}_n$.** Let $\varphi$ be a cusp form on $\mathrm{GL}_n(\mathbb{A})$ with central character $\omega$, and write
   $\lvert \omega(z) \rvert = \lvert z \rvert^{\sigma}$ with $\sigma$ real. Then $\varphi \cdot \lvert \det \rvert^{-\sigma/n}$ is a cusp form
   with unitary central character; a cusp form with unitary central character is bounded and rapidly
   decreasing on Siegel sets of $\mathrm{GL}_n(\mathbb{A})^1$, and if $\omega$ is unitary then $\mathcal{A}_0(\omega)$ is contained in
   $L^2_0(\omega)$. (The exponent $\sigma$ need not be an integer: on $\mathrm{GL}_1$, which has no proper parabolic
   subgroup, $z \mapsto \lvert z \rvert^{1/2}$ is a cusp form.)

4. **Uniform bound for convolutions** (Gelfand–Piatetski-Shapiro). For $f \in C^\infty_c(G(\mathbb{A})^1)$ there is a constant
   $c_f$ such that $\sup_x \lvert (R(f)\varphi)(x) \rvert \le c_f \lVert \varphi \rVert_2$ for every cuspidal function $\varphi \in L^2(G(k) \backslash G(\mathbb{A})^1)$, where
   $R(f)\varphi(x) = \int f(y) \varphi(xy)\, dy$; in fact, for every Siegel set $\mathfrak{S}$, $\varphi \mapsto R(f)\varphi$ is continuous from the cuspidal $L^2$
   space to the space of functions rapidly decreasing on $\mathfrak{S}^1$, with the seminorms
   $\sup_{x \in \mathfrak{S}^1} \lVert x \rVert^N \lvert (D R(f)\varphi)(x) \rvert$ for left invariant differential operators $D$ (the weighted supremum is taken over
   the Siegel set, as in the definition above, not over all of $G(\mathbb{A})^1$: the height $\lVert \cdot \rVert$ is not invariant under $G(k)$,
   and for $G = \mathbb{G}_m$ over $\mathbb{Q}$ and $\varphi = 1$ the supremum over all points would be infinite for every $N > 0$).

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-and-automorphic-representations.md), for automorphic forms, cusp forms, constant terms, the height and $L^2_0(\omega)$
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for Siegel sets and $G(\mathbb{A})^1$

## Proof depends on

- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the covering of $G(k) \backslash G(\mathbb{A})^1$ by a Siegel set, on which the estimates are made, and the properties of the height
- [Constant terms and Harish-Chandra's convolution identity for automorphic forms](constant-terms-and-convolution-identity.md), for Harish-Chandra's convolution identity $\varphi = \varphi \star \alpha$ for $K$-finite, $\mathcal{Z}$-finite functions (Borel, §4.2), from which uniform moderate growth (item 1) follows since $D(\varphi \star \alpha) = \varphi \star D\alpha$ (Borel, §4.3), and for the reduction along the split centre

## Sources

- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §13, the definitions of rapidly decreasing
  and uniformly tempered functions, the truncation operator (13.1) with "if $\varphi$ belongs to
  $L^2_{\mathrm{cusp}}$, then $\Lambda^T\varphi = \varphi$", and Proposition 13.2 (a) ($\Lambda^T\varphi$ is
  rapidly decreasing for uniformly tempered $\varphi$).
- A. Borel, "Automorphic forms on reductive groups", lecture notes (Park City),
  <http://homepages.math.uic.edu/~rtakloo/papers/borel/borel3.pdf>: §4.1–4.3 (analyticity, the theorem on
  $f \star \alpha = f$ and its Corollary: an automorphic form is of uniform moderate growth), §7.7–7.9 (the
  basic estimate and Theorem 7.9, "Any cusp form is fast decreasing", with the seminorms of §6.4 taken on Siegel
  sets), §9.3, (67) (continuity of the
  composition from the cuspidal $L^2$ space to rapidly decreasing functions) and (68) (the uniform bound of
  item 4), stated for $\Gamma \backslash G$ with $\Gamma$ arithmetic, the adelic form following by the finiteness of class
  numbers.
- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 2, §3 ("By a
  theorem of Harish-Chandra we know that $K_\infty$-finiteness implies uniform moderate growth"), §5,
  Theorem 2.2 (Gelfand and Piatetski-Shapiro) and the paragraph after it ($\mathcal{A}_0(\omega) \subset \mathcal{A}^\infty_0(\omega) \subset L^2_0(\omega)$
  for unitary $\omega$; the integer exponent in the printed statement of Theorem 2.2 cannot hold for every
  non-unitary central character, and is replaced here by the reduction to the unitary case); Lecture 3,
  §4, the last paragraph (every cuspidal representation is an unramified twist of a unitary one).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states forms of this result for unitary groups of CM extensions as
  `GlobalTheory.Published.CuspRapidDecay`, `GlobalTheory.Published.CuspBounded`,
  `GlobalTheory.Published.CuspDecayBound` and `GlobalTheory.Published.CuspDecaySobolev`, and for
  $\mathrm{GL}_n$ as `GlobalTheory.Published.CuspFormsBoundedGL`.
