# Eisenstein series and their meromorphic continuation

This node is still to be broken down. It covers Langlands's theory of Eisenstein series on a connected
reductive group $G$ over a number field $k$, as it is used for the analysis of
[Siegel Eisenstein series](../theta-correspondence/siegel-eisenstein-series-on-unitary-groups.md) and for
the characterization of
[automorphic representations as constituents of induced representations](automorphic-representations-as-constituents-of-induced-representations.md).
For a standard parabolic subgroup $P = M_P N_P$ over $k$, let $\mathcal{H}_P$ be the Hilbert space of
functions $\varphi$ on $N_P(\mathbb{A}) M_P(k) A_P(\mathbb{R})^0 \backslash G(\mathbb{A})$ such that, for each $x \in G(\mathbb{A})$,
$m \mapsto \varphi(mx)$ on $M_P(k) \backslash M_P(\mathbb{A})^1$ lies in the discrete spectrum, with
$\lVert \varphi \rVert^2 = \int_K \int_{M_P(k) \backslash M_P(\mathbb{A})^1} \lvert \varphi(mk) \rvert^2\, dm\, dk < \infty$; let $\mathcal{H}_P^0$ be its
dense subspace of $K$-finite vectors lying in finite sums of irreducible subspaces (smooth functions, to
which the formulas below apply pointwise), $\mathcal{H}_{P,\mathrm{cusp}}^0$ the cuspidal ones, and $\rho_P$, $H_P$,
$\mathfrak{a}_P$ and $\mathfrak{a}_{P,\mathbb{C}}^*$ as usual.

- **Definition and convergence** (Godement, Langlands). For $\varphi \in \mathcal{H}_P^0$, the Eisenstein series
  $E(x, \varphi, \lambda) = \sum_{\delta \in P(k) \backslash G(k)} \varphi(\delta x)\, e^{(\lambda + \rho_P)(H_P(\delta x))}$ and the
  intertwining operators $M(s, \lambda)$, $s \in W(\mathfrak{a}_P, \mathfrak{a}_{P'})$, converge absolutely
  for $\operatorname{Re} \lambda \in \rho_P + (\mathfrak{a}_P^*)^+$, to analytic functions of $\lambda$.
- **Meromorphic continuation and functional equations** (Langlands). $E(x, \varphi, \lambda)$ and
  $M(s, \lambda)\varphi$ continue meromorphically to $\mathfrak{a}_{P,\mathbb{C}}^*$, with
  $E(x, M(s, \lambda)\varphi, s\lambda) = E(x, \varphi, \lambda)$ and $M(ts, \lambda) = M(t, s\lambda) M(s, \lambda)$;
  they are analytic on $i\mathfrak{a}_P^*$, where $M(s, \lambda)$ is unitary.
- **Constant terms and automorphy.** For $\varphi \in \mathcal{H}_{P,\mathrm{cusp}}^0$ and a standard parabolic subgroup
  $Q$, the constant term $\int_{N_Q(k) \backslash N_Q(\mathbb{A})} E(nx, \varphi, \lambda)\, dn$ is
  $\sum_{s \in W(\mathfrak{a}_P, \mathfrak{a}_Q)} (M(s, \lambda)\varphi)(x)\, e^{(s\lambda + \rho_Q)(H_Q(x))}$ if $Q$ is associated to $P$
  and in general
  $\sum_{s \in W(P; Q)} E^Q(x, M(s, \lambda)\varphi, s\lambda)$, a sum of Eisenstein series of the Levi factor of $Q$
  (for $Q = G$ it is the Eisenstein series itself). Away from its poles, the Eisenstein series of a
  $K$-finite cuspidal datum is an automorphic form.
- **Spectral decomposition** (Langlands). The orthogonal decomposition
  $L^2(G(k) \backslash G(\mathbb{A})) = \bigoplus_{\mathcal{P}} L^2_{\mathcal{P}}$ over associated classes of parabolic
  subgroups, through wave packets of Eisenstein series, and the residual spectrum as iterated residues.
- **Vanishing lemma** (Langlands). An automorphic form whose constant terms along all parabolic
  subgroups (including $G$) are orthogonal to cusp forms is zero.

## Expansion

A good expansion has pages for the definition and absolute convergence of Eisenstein series and
intertwining operators, for the constant term formula, for the meromorphic continuation and functional
equations, for the automorphy of Eisenstein series, for the spectral decomposition, and for the vanishing
lemma. The spectral decomposition should follow Langlands's route through wave packets: for a
Paley–Wiener function $\Psi(\lambda)$ with values in a finite-dimensional subspace of the space of cuspidal data
$\mathcal{H}^0_{P,\mathrm{cusp},\sigma}$ (which itself need not be finite-dimensional; Arthur, §12, pp. 65–66), the
pseudo-Eisenstein series $E\psi$ of $\psi(x) = \int_{\Lambda + i\mathfrak{a}_P^*} e^{(\lambda + \rho_P)(H_P(x))} \Psi(\lambda, x)\, d\lambda$ is square integrable (Arthur's Lemma 12.2),
the inner product formula (12.3) for two such series holds with $\Lambda$ in the cone of absolute convergence of the
intertwining operators (Lemma 12.3), and $L^2(G(k) \backslash G(\mathbb{A}))$ is the orthogonal sum of the closed subspaces generated
by the wave packets of the classes of cuspidal data (Lemma 12.4); the continuation and the decomposition of
each summand then come from moving the contour in (12.3) to $i\mathfrak{a}_P^*$ and analysing the residues. These pages
should cite Langlands's *On the functional equations satisfied by Eisenstein series* (Lecture Notes in
Math. 544, Springer, 1976) and Mœglin–Waldspurger's *Spectral decomposition and Eisenstein series*
(Cambridge, 1995) with locators, besides the sources below.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-and-automorphic-representations.md), for automorphic forms, cusp forms and constant terms
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for $H_P$, $\mathfrak{a}_P$ and the definition of Siegel sets

## Proof depends on

- [Constant terms and Harish-Chandra's convolution identity for automorphic forms](constant-terms-and-convolution-identity.md), for the automorphy of constant terms of automorphic forms on Levi factors, applied once an Eisenstein series is known to be automorphic, in the analysis along smaller parabolic subgroups; the constant term formula itself comes from the Bruhat decomposition and unfolding
- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for the decomposition of $G(k)$ into the double cosets $P(k) w Q(k)$, which unfolds the constant terms
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the Siegel-set estimates in the proof of absolute convergence
- [Discreteness of the cuspidal spectrum](discreteness-of-the-cuspidal-spectrum.md), for the cuspidal spectrum of the Levi factors, whose cuspidal data index the wave packets of the spectral decomposition
- [Paley–Wiener theorem on a real vector space](../../../Analysis/harmonic-analysis/fourier-transform/paley-wiener-theorem-on-a-real-vector-space.md), for the wave packets: entire functions on $\mathfrak{a}_{P,\mathbb{C}}^*$ of Paley–Wiener type, with values in a finite-dimensional space, are the Fourier–Laplace transforms of smooth compactly supported functions on $\mathfrak{a}_P$ (Arthur, §12)
- [Square-integrable K-finite and Z-finite functions are automorphic forms](square-integrable-automorphic-forms.md), for the smooth representatives of moderate growth of the $K$-finite vectors in the discrete spectrum of the Levi factors, to which the formulas apply pointwise, and for their growth on Siegel sets in the proof of absolute convergence (Arthur, §7, Lemma 7.1, pp. 32–35)
- [Rapid decay of cusp forms](rapid-decay-of-cusp-forms.md), for the rapid decay of cuspidal data on Siegel sets of the Levi factors, behind the square integrability of the pseudo-Eisenstein series and the inner products of wave packets (Arthur, §12, pp. 64–66)
- [Harish-Chandra's finiteness theorem for automorphic forms](harish-chandra-finiteness-theorem.md), for the finite multiplicities in the whole discrete spectrum of the Levi factors, residual part included (Borel, §10, p. 28)

## Sources

- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §7 (the space $\mathcal{H}_P$ and its subspace
  $\mathcal{H}_P^0$), (7.1)–(7.2), Lemma 7.1 (Langlands; absolute convergence for $\varphi \in \mathcal{H}_P^0$), Theorem 7.2
  (Langlands; meromorphic continuation, (7.3)–(7.4), unitarity on $i\mathfrak{a}_P^*$, the decomposition (7.5)), §12,
  (12.2) and Lemmas 12.2–12.4 (Langlands: the wave packets, their square integrability, the inner product
  formula (12.3) and the orthogonal decomposition (12.4)) with the discussion after them, p. 66 (their use for
  Theorem 7.2), and §15, the formula before (15.3) for associated $Q$ and (15.3)
  for arbitrary $Q$ (constant terms of cuspidal Eisenstein series).
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
