# Jacquet modules of the Weil representation and degenerate principal series

This node is still to be broken down. It covers the structure of the local
[Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md) and of the
degenerate principal series over a local field $F$ of characteristic $0$, mostly non-archimedean, that
the proofs of [Howe duality](howe-duality-over-p-adic-fields.md), the analysis of
[Siegel Eisenstein series](siegel-eisenstein-series-on-unitary-groups.md) and the
[Siegel–Weil formula](siegel-weil-formula-convergent-range.md) use. Let $E/F$ be a quadratic extension,
$W_n$ a skew-Hermitian space of dimension $n$, $V_m$ a Hermitian space of dimension $m$ with Witt index
$q$, and $\omega_{W_n, V_m}$ their Weil representation.

- **Kudla's filtration.** For an isotropic subspace $X_a \subset W_n$ of dimension $a$ with stabilizer
  $Q(X_a)$ and Levi factor $\mathrm{GL}(X_a) \times \mathrm{U}(W_{n-2a})$, the Jacquet module
  $R_{Q(X_a)}(\omega_{W_n, V_m})$ has an equivariant filtration $R_0 \supset R_1 \supset \dots \supset R_a \supset 0$
  whose successive quotients $J_k$ are parabolically induced from
  $\chi_V \lvert \det_{X_{a-k}} \rvert^{\lambda_{a-k}} \otimes C^\infty_c(\mathrm{Isom}_{E,c}(X_k, Y_k)) \otimes \omega_{W_{n-2a}, V_{m-2k}}$,
  with $\lambda_{a-k} = s_{m,n} + \tfrac{a-k}{2}$, $s_{m,n} = \tfrac{m-n}{2}$, $Y_k \subset V_m$ isotropic
  of dimension $k$, and $J_k = 0$ for $k > \min(a, q)$.
- **Degenerate principal series.** On the doubled space $W_n + W_n^-$, the restriction to
  $\mathrm{U}(W_n) \times \mathrm{U}(W_n^-)$ of $I(s) = \mathrm{Ind}_{Q(\Delta W_n)}^{\mathrm{U}(W_n + W_n^-)} \chi_V \lvert \det \rvert^s$
  has an equivariant filtration by orbits (Kudla–Rallis); the points of reducibility of the Siegel
  degenerate principal series $I_n(s, \chi)$ of a split $\mathrm{U}(W_{2n})$ and the irreducibility of its
  submodules $R_n(V)$ in the relevant cases (Kudla–Sweet; Lee–Zhu and Ichino over $\mathbb{R}$); Rallis's
  embedding of the maximal $\mathrm{U}(V)$-invariant quotient $R_n(V)$ of the Weil representation into
  $I_n(s_{m,n}, \chi_V)$ through $\varphi \mapsto (g \mapsto \omega(g)\varphi(0))$; and the invariant
  distribution theorem (Mœglin–Vignéras–Waldspurger, Lee–Zhu) through which intertwining maps from the
  local Weil representation arising from Siegel Eisenstein series factor through $R_n(V)$.
- **The MVW involution.** The covariant functor $\pi \mapsto \pi^{\mathrm{MVW}}$ of Mœglin, Vignéras and
  Waldspurger on smooth representations of unitary groups, with $\pi^{\mathrm{MVW}} \cong \pi^\vee$ for
  irreducible $\pi$, and its compatibility with the Weil representation.
- **Bernstein's second adjointness.** For a parabolic subgroup $P = MN$ with opposite $\bar P$,
  $\mathrm{Hom}_G(\mathrm{Ind}_P^G \sigma, \pi) \cong \mathrm{Hom}_M(\sigma, R_{\bar P}(\pi))$ (Bernstein's
  Frobenius reciprocity), which Gan and Takeda use with the standard one.

A good expansion has pages for Kudla's filtration of the Jacquet modules of the Weil representation, for
the orbit filtration of the doubled degenerate principal series, for the reducibility points and module
structure of the Siegel degenerate principal series $I_n(s, \chi)$ (non-archimedean and archimedean), for
Rallis's embedding $R_n(V) \hookrightarrow I_n(s_{m,n}, \chi_V)$, for the invariant distribution theorem,
for the MVW involution and for Bernstein's second adjointness, each with a precise statement and the
sources below.

## Depends on

- [Splitting characters and the Weil representation of unitary dual pairs](weil-representation-of-unitary-dual-pairs.md), for the local Weil representation
- [Parabolic induction and Jacquet functors](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md), for Jacquet modules and induced representations

## Sources

- W. T. Gan and S. Takeda, "A proof of the Howe duality conjecture", J. Amer. Math. Soc. 29 (2016),
  473–493, arXiv:1407.1995 (version 4): §2.4 (Bernstein's Frobenius reciprocity), §2.7 (the MVW involution, after [MVW, p. 91]), §3.1, Lemma 3.1
  (Kudla's filtration, citing S. S. Kudla, "On the local theta-correspondence", Invent. Math. 83 (1986),
  229–255, and W. T. Gan and A. Ichino, Lemma C.2), §3.2, Lemma 3.2 (the restriction of the doubled
  degenerate principal series, after Kudla and Rallis).
- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity) and
  the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709 (version 3):
  Proposition 5.1 (reducibility points, citing Kudla–Rallis, Kudla–Sweet, Sweet and Yamana), §5.3–5.4
  (Siegel–Weil sections and Rallis's embedding $R_n(V_r) \hookrightarrow I_n^n(s, \chi)$), Propositions 5.2–5.3
  (module structure).
- S. S. Kudla, "Notes on the local theta correspondence", lecture notes, European School in Group
  Theory, 1996, <https://www.math.toronto.edu/~skudla/castle.pdf>: §III.8 (Jacquet functors of the Weil
  representation, for symplectic–orthogonal pairs) and Chapter IV (seesaw dual pairs and degenerate
  principal series).
- S. Yamana, "The Siegel–Weil formula for unitary groups", Pacific J. Math. 264 (2013), 235–257,
  <https://doi.org/10.2140/pjm.2013.264.235>: the remark after Theorem 2 (the local facts, from S. S.
  Kudla and W. J. Sweet, Israel J. Math. 98 (1997), A. Ichino, Math. Z. 255 (2007), and S. T. Lee and
  C.-B. Zhu, 1998) and the proof of Theorem 2 in §3 (the invariant distribution theorem, Kudla–Sweet's
  Theorem 1.2, Ichino's Proposition 2.2).
- C. Mœglin, M.-F. Vignéras and J.-L. Waldspurger, *Correspondances de Howe sur un corps p-adique*,
  Lecture Notes in Math. 1291, Springer, 1987, p. 91 (the involution), as cited by Gan and Takeda.
