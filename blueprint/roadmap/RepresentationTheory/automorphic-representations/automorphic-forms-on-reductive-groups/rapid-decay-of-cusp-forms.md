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
3. **$\mathrm{GL}_n$.** If $\varphi$ is a cusp form on $\mathrm{GL}_n(\mathbb{A})$ with central character, there is
   an integer $r$ such that $\lvert \varphi(zg) \rvert \le C_N \lvert z \rvert^{r} \lVert g \rVert^{-N}$ for all $N$,
   for $z$ in the centre and $g$ in a fundamental domain intersected with $\mathrm{SL}_n(\mathbb{A})$; if the
   central character $\omega$ is unitary, then $\mathcal{A}_0(\omega)$ is contained in $L^2_0(\omega)$.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-and-automorphic-representations.md), for automorphic forms, cusp forms, constant terms, the height and $L^2_0(\omega)$
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for Siegel sets and $G(\mathbb{A})^1$

## Proof depends on

- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the covering of $G(k) \backslash G(\mathbb{A})^1$ by a Siegel set, on which the estimates are made, and the properties of the height
- [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for the analyticity of $K$-finite, $\mathcal{Z}$-finite functions (matrix coefficients of Harish-Chandra modules), behind Harish-Chandra's convolution theorem $\varphi = \varphi \star \alpha$ used for item 1

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
  basic estimate and Theorem 7.9, "Any cusp form is fast decreasing").
- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 2, §3 ("By a
  theorem of Harish-Chandra we know that $K_\infty$-finiteness implies uniform moderate growth"), §5,
  Theorem 2.2 (Gelfand and Piatetski-Shapiro) and the paragraph after it ($\mathcal{A}_0(\omega) \subset \mathcal{A}^\infty_0(\omega) \subset L^2_0(\omega)$).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states forms of this result for unitary groups of CM extensions as
  `GlobalTheory.Published.CuspRapidDecay`, `GlobalTheory.Published.CuspBounded`,
  `GlobalTheory.Published.CuspDecayBound` and `GlobalTheory.Published.CuspDecaySobolev`, and for
  $\mathrm{GL}_n$ as `GlobalTheory.Published.CuspFormsBoundedGL`.
