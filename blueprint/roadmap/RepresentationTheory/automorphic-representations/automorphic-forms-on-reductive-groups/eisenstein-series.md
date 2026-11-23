# Eisenstein series and their meromorphic continuation

This node is still to be broken down. It covers Langlands's theory of Eisenstein series on a connected
reductive group $G$ over a number field $k$, as it is used for the analysis of
[Siegel Eisenstein series](../theta-correspondence/siegel-eisenstein-series-on-unitary-groups.md) and for
the characterization of
[automorphic representations as constituents of induced representations](automorphic-representations-as-constituents-of-induced-representations.md).
For a standard parabolic subgroup $P = M_P N_P$ over $k$, let $\mathcal{H}_P$ be the Hilbert space of
functions $\varphi$ on $N_P(\mathbb{A}) M_P(k) A_P(\mathbb{R})^0 \backslash G(\mathbb{A})$ whose restrictions to
$M_P(\mathbb{A})^1$ lie in the discrete spectrum, $\mathcal{H}_P^0$ its dense subspace of $K$-finite vectors in
finite sums of irreducible subspaces, and $\rho_P$, $H_P$ and $\mathfrak{a}_{P,\mathbb{C}}^*$ as usual.

- **Definition and convergence** (Godement, Langlands). The Eisenstein series
  $E(x, \varphi, \lambda) = \sum_{\delta \in P(k) \backslash G(k)} \varphi(\delta x)\, e^{(\lambda + \rho_P)(H_P(\delta x))}$ and the
  intertwining operators $M(s, \lambda)$, $s \in W(\mathfrak{a}_P, \mathfrak{a}_{P'})$, converge absolutely
  for $\operatorname{Re} \lambda \in \rho_P + (\mathfrak{a}_P^*)^+$, to analytic functions of $\lambda$.
- **Meromorphic continuation and functional equations** (Langlands). $E(x, \varphi, \lambda)$ and
  $M(s, \lambda)\varphi$ continue meromorphically to $\mathfrak{a}_{P,\mathbb{C}}^*$, with
  $E(x, M(s, \lambda)\varphi, s\lambda) = E(x, \varphi, \lambda)$ and $M(ts, \lambda) = M(t, s\lambda) M(s, \lambda)$;
  they are analytic on $i\mathfrak{a}_P^*$, where $M(s, \lambda)$ is unitary.
- **Constant terms and automorphy.** The constant term of $E(x, \varphi, \lambda)$ along a standard
  parabolic subgroup is given by the intertwining operators (for cuspidal $\varphi$, the sum over
  $s \in W(\mathfrak{a}_P, \mathfrak{a}_{P'})$ of the terms $M(s, \lambda)\varphi$); away from its poles, the
  Eisenstein series of a $K$-finite cuspidal datum is an automorphic form.
- **Spectral decomposition** (Langlands). The orthogonal decomposition
  $L^2(G(k) \backslash G(\mathbb{A})) = \bigoplus_{\mathcal{P}} L^2_{\mathcal{P}}$ over associated classes of parabolic
  subgroups, through wave packets of Eisenstein series, and the residual spectrum as iterated residues.
- **Vanishing lemma** (Langlands). An automorphic form whose constant terms along all parabolic
  subgroups (including $G$) are orthogonal to cusp forms is zero.

A good expansion has pages for the definition and absolute convergence of Eisenstein series and
intertwining operators, for the constant term formula, for the meromorphic continuation and functional
equations, for the automorphy of Eisenstein series, for the spectral decomposition, and for the vanishing
lemma, citing Langlands's *On the functional equations satisfied by Eisenstein series* (Lecture Notes in
Math. 544, Springer, 1976) and Mœglin–Waldspurger's *Spectral decomposition and Eisenstein series*
(Cambridge, 1995) with locators, besides the sources below.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-and-automorphic-representations.md), for automorphic forms, cusp forms and constant terms
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for $H_P$, $\mathfrak{a}_P$ and the Siegel sets on which the convergence is proved

## Sources

- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §7, (7.1)–(7.2), Lemma 7.1 (Langlands;
  absolute convergence), Theorem 7.2 (Langlands; meromorphic continuation, (7.3)–(7.4), unitarity on
  $i\mathfrak{a}_P^*$, the decomposition (7.5)), and §12, (12.2) and Lemmas 12.2–12.4 (Langlands).
- A. Borel, "Automorphic forms on reductive groups", lecture notes (Park City),
  <http://homepages.math.uic.edu/~rtakloo/papers/borel/borel3.pdf>: §8.6 (the residual and continuous
  spectra, "analyzed by means of the analytic continuation of Eisenstein series").
- R. P. Langlands, "On the notion of an automorphic representation", Proc. Sympos. Pure Math. 33,
  Part 1, 1979, 203–207,
  <https://sunsite.ubc.ca/DigitalMathArchive/Langlands/pdf/notion-ps.pdf>: Lemma 5 ("If $\varphi \perp P$ for all
  $P$ then $\varphi$ is zero", recalled from Langlands's monograph) and the proof of Proposition 2 (the use of
  Eisenstein series for the converse direction).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses these results through its statements on Siegel Eisenstein series of unitary groups
  (`GlobalTheory.Published.SiegelEisensteinContinuation`, `GlobalTheory.Published.DoublingMethod`).
