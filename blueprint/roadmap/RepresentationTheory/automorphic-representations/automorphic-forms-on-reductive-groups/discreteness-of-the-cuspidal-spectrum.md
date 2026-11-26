# Discreteness of the cuspidal spectrum

Let $k$ be a number field, $G$ a connected reductive group over $k$ and
$G(\mathbb{A})^1 = \{x \in G(\mathbb{A}) : H_G(x) = 0\}$. A function $\varphi$ in
$L^2(G(k) \backslash G(\mathbb{A})^1)$ is cuspidal if $\int_{N_P(k) \backslash N_P(\mathbb{A})} \varphi(nx)\, dn = 0$, over the
compact quotient, for every proper parabolic subgroup $P = M_P N_P$ of $G$ over $k$ and almost every $x$. The cuspidal functions form a closed
subspace $L^2_{\mathrm{cusp}}$, invariant under right translation by $G(\mathbb{A})^1$; for
$f \in C^\infty_c(G(\mathbb{A})^1)$ let $R_{\mathrm{cusp}}(f)$ be the restriction of
$R(f)\varphi(x) = \int f(y) \varphi(xy)\, dy$ to it.

1. **Hilbert–Schmidt and trace class** (Gelfand–Piatetski-Shapiro). For every
   $f \in C^\infty_c(G(\mathbb{A})^1)$, $R_{\mathrm{cusp}}(f)$ is a Hilbert–Schmidt operator, and it is of trace
   class.
2. **Discrete decomposition** (Gelfand–Piatetski-Shapiro). $L^2_{\mathrm{cusp}}$ decomposes under
   $G(\mathbb{A})^1$ into a Hilbert direct sum of irreducible unitary representations, each occurring with
   finite multiplicity.
3. **$\mathrm{GL}_n$.** For a unitary character $\omega$ of the idele class group,
   $L^2_0(\omega) = \widehat{\bigoplus}_\pi m(\pi) V_\pi$ with $m(\pi) < \infty$, and the space of cusp forms with
   central character $\omega$ is $\mathcal{A}_0(\omega) = \bigoplus_\pi m(\pi) (V_\pi)_K$, the algebraic direct sum, over the irreducible
   summands, of their $K$-finite vectors; the unitary cuspidal automorphic representations are the $(V_\pi)_K$.
   The $K$-finite vectors of the whole Hilbert sum can form a larger space: for $\mathrm{GL}_2$, an infinite
   square-summable sum of spherical cusp forms of one level with distinct Casimir eigenvalues is $K$-fixed but not
   finite under the centre of the enveloping algebra (for $\mathrm{GL}_1$ with a fixed central character both spaces are
   the line of that character).

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-and-automorphic-representations.md), for cusp forms, $L^2_0(\omega)$ and cuspidal automorphic representations
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for $G(\mathbb{A})^1$ and the finite volume of $G(k) \backslash G(\mathbb{A})^1$, which makes $L^2_{\mathrm{cusp}}$ meaningful as a space of square-integrable functions

## Proof depends on

- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the covering of $G(k) \backslash G(\mathbb{A})^1$ by a Siegel set, on which the kernel of $R_{\mathrm{cusp}}(f)$ is estimated
- [Rapid decay of cusp forms](rapid-decay-of-cusp-forms.md), for its item 4, the quantitative uniform bound $\sup_x \lvert (R(f)\varphi)(x) \rvert \le c_f \lVert \varphi \rVert_2$ for cuspidal $\varphi \in L^2$ (Borel, §9.3, (67)–(68)), the estimate that gives the Hilbert–Schmidt property, and for the inclusion $\mathcal{A}_0(\omega) \subset L^2_0(\omega)$ used in item 3
- [Dixmier–Malliavin theorem](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/dixmier-malliavin-theorem.md), in its form for functions, writing $f \in C^\infty_c(G(\mathbb{A})^1)$ as a finite sum $\sum_i g_i * h_i$ of convolutions of functions in the same space (after reduction to functions bi-invariant under an open compact subgroup $K_0$ of $G(\mathbb{A}_f)$: the compact support of $f$ meets finitely many double cosets $K_0 g K_0$, on each of which $f$ is given by a function on a translate of the Lie group $G_\infty^1 = G_\infty \cap G(\mathbb{A})^1$, to which the theorem is applied), which turns the Hilbert–Schmidt property of the $R_{\mathrm{cusp}}(g_i)$, $R_{\mathrm{cusp}}(h_i)$ into the trace-class property of $R_{\mathrm{cusp}}(f)$
- [Harish-Chandra's finiteness theorem for automorphic forms](harish-chandra-finiteness-theorem.md), for the finite multiplicities and for the identification of $\mathcal{A}_0(\omega)$ with the algebraic direct sum, over the irreducible summands of $L^2_0(\omega)$, of their $K$-finite vectors: those are $\mathcal{Z}$-finite, the centre acting on an irreducible summand by scalars, hence cusp forms; conversely, the projections of a cusp form to the summands have its $K$-types and are annihilated by its ideal of finite codimension in $\mathcal{Z}$, and the space of such cuspidal functions is finite-dimensional, so only finitely many projections are non-zero (the $K$-finite vectors of the whole Hilbert sum are not used)
- [Square-integrable K-finite and Z-finite functions are automorphic forms](square-integrable-automorphic-forms.md), for the regularity of the $K$-finite vectors of the irreducible summands of $L^2_0(\omega)$, which are $\mathcal{Z}$-finite, hence smooth of moderate growth and cusp forms

## Sources

- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §12, (12.1) (where the integral over $N_P(\mathbb{A})$ is
  to be read over $N_P(\mathbb{Q}) \backslash N_P(\mathbb{A})$, as in §13, (13.1)) and Theorem 12.1 (Gelfand, Piatetski-Shapiro)
  with its proof (Hilbert–Schmidt class of $R_{\mathrm{cusp}}(f)$ from (12.1) and
  Theorem 8.1, then the spectral theorem).
- A. Borel, "Automorphic forms on reductive groups", lecture notes (Park City),
  <http://homepages.math.uic.edu/~rtakloo/papers/borel/borel3.pdf>: §9.3, (67)–(68), the Theorem
  (Gelfand–Piatetski-Shapiro: $\star\alpha$ is Hilbert–Schmidt), the remark that with the theorem of
  Dixmier–Malliavin "the operator $\star\alpha$ is of trace class", and the Corollary (discrete
  decomposition with finite multiplicities); §8.6, pp. 27–28 (the $K$-finite vectors of an irreducible subspace are
  $K$-finite and $\mathcal{Z}$-finite, hence automorphic forms; finite multiplicities from Theorem 8.4).
- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 3, §4,
  Theorem 3.7, Definitions 3.5 and 3.6 and the paragraph between them
  ($\mathcal{A}_0(\omega) = \oplus m(\pi) (V_\pi)_K$; the printed shorthand $\mathcal{A}_0(\omega) = \mathcal{A}^\infty_0(\omega)_K = L^2_0(\omega)_K$ is to be read with
  $(\cdot)_K$ the algebraic direct sum of the $K$-finite vectors of the irreducible summands, since the $K$-finite vectors of
  the whole Hilbert sum can form a larger space).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states item 1 for unitary groups of CM extensions as `GlobalTheory.Published.CuspTraceClass` and
  item 3 for $\mathrm{GL}_n$ as `GlobalTheory.Published.CuspidalSpectrumGL` (discrete decomposition, finite
  vectors and boundedness of cusp forms).
