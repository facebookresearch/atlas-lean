# Discreteness of the cuspidal spectrum

Let $k$ be a number field, $G$ a connected reductive group over $k$ and
$G(\mathbb{A})^1 = \{x \in G(\mathbb{A}) : H_G(x) = 0\}$. A function $\varphi$ in
$L^2(G(k) \backslash G(\mathbb{A})^1)$ is cuspidal if $\int_{N_P(\mathbb{A})} \varphi(nx)\, dn = 0$ for every proper
parabolic subgroup $P = M_P N_P$ of $G$ over $k$ and almost every $x$. The cuspidal functions form a closed
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
   central character $\omega$ is $\mathcal{A}_0(\omega) = \bigoplus_\pi m(\pi) (V_\pi)_K$, the direct sum of the
   $K$-finite vectors; the unitary cuspidal automorphic representations are the $(V_\pi)_K$.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-and-automorphic-representations.md), for cusp forms, $L^2_0(\omega)$ and cuspidal automorphic representations
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for $G(\mathbb{A})^1$ and the finite volume of $G(k) \backslash G(\mathbb{A})^1$, which makes $L^2_{\mathrm{cusp}}$ meaningful as a space of square-integrable functions

## Proof depends on

- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the covering of $G(k) \backslash G(\mathbb{A})^1$ by a Siegel set, on which the kernel of $R_{\mathrm{cusp}}(f)$ is estimated
- [Rapid decay of cusp forms](rapid-decay-of-cusp-forms.md), for the uniform bound $\lvert (\varphi * f)(x) \rvert \le c \lVert \varphi \rVert_2$ on cuspidal functions, the estimate that gives the Hilbert–Schmidt property, and for the inclusion $\mathcal{A}_0(\omega) \subset L^2_0(\omega)$ used in item 3
- [Dixmier–Malliavin theorem](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/dixmier-malliavin-theorem.md), for writing $f$ as a finite sum of convolutions, which turns the Hilbert–Schmidt property into the trace-class property
- [Harish-Chandra's finiteness theorem for automorphic forms](harish-chandra-finiteness-theorem.md), for the finite multiplicities and the identification of the $K$-finite vectors of $L^2_0(\omega)$ with $\mathcal{A}_0(\omega)$

## Sources

- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §12, (12.1) and Theorem 12.1 (Gelfand,
  Piatetski-Shapiro) with its proof (Hilbert–Schmidt class of $R_{\mathrm{cusp}}(f)$ from (12.1) and
  Theorem 8.1, then the spectral theorem).
- A. Borel, "Automorphic forms on reductive groups", lecture notes (Park City),
  <http://homepages.math.uic.edu/~rtakloo/papers/borel/borel3.pdf>: §9.3, (67)–(68), the Theorem
  (Gelfand–Piatetski-Shapiro: $\star\alpha$ is Hilbert–Schmidt), the remark that with the theorem of
  Dixmier–Malliavin "the operator $\star\alpha$ is of trace class", and the Corollary (discrete
  decomposition with finite multiplicities); §8.6 (finite multiplicities from Theorem 8.4).
- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 3, §4,
  Theorem 3.7, Definitions 3.5 and 3.6 and the paragraph between them
  ($\mathcal{A}_0(\omega) = \mathcal{A}^\infty_0(\omega)_K = L^2_0(\omega)_K$ and $\mathcal{A}_0(\omega) = \oplus m(\pi) (V_\pi)_K$).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states item 1 for unitary groups of CM extensions as `GlobalTheory.Published.CuspTraceClass` and
  item 3 for $\mathrm{GL}_n$ as `GlobalTheory.Published.CuspidalSpectrumGL` (discrete decomposition, finite
  vectors and boundedness of cusp forms).
