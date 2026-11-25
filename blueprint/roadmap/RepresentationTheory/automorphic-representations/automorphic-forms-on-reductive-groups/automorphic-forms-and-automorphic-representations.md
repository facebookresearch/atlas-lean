# Automorphic forms, cusp forms and automorphic representations

Let $k$ be a number field with adele ring $\mathbb{A} = k_\infty \times \mathbb{A}_f$, $G$ a connected
reductive group over $k$, $G_\infty = \prod_{v \mid \infty} G(k_v)$ and $G_f = G(\mathbb{A}_f)$. Fix a maximal
compact subgroup $K = K_\infty K_f$ of $G(\mathbb{A})$, with $K_f = \prod_{v < \infty} K_v$ open in $G_f$, let
$\mathfrak{g}$ be the complexified Lie algebra of $G_\infty$, $\mathcal{U}(\mathfrak{g})$ its enveloping algebra
and $\mathcal{Z}$ the centre of $\mathcal{U}(\mathfrak{g})$ (not to be confused with the centre of $G$). Fix a faithful
representation $r \colon G \to \mathrm{GL}_m$ over $k$ and the two-sided height

$$\lVert x \rVert = \prod_v \max_{i,j}\bigl(\lvert r(x)_{ij} \rvert_v, \lvert (r(x)^{-1})_{ij} \rvert_v\bigr), \qquad x \in G(\mathbb{A}),$$

which takes into account the entries of $r(x)$ and of its inverse (with only the entries of $r(x)$, every
element of $\mathbb{Q}^\times = \mathrm{GL}_1(\mathbb{Q})$ would have height $1$ by the product formula); its balls are
compact and changing $r$ changes it by bounded powers. A function on $G(\mathbb{A})$ is
smooth if it is $C^\infty$ in the variable of $G_\infty$ and locally constant in the variable of $G_f$.

- **Automorphic forms.** An automorphic form on $G(\mathbb{A})$ is a smooth function
  $\varphi \colon G(\mathbb{A}) \to \mathbb{C}$ such that (i) $\varphi(\gamma g) = \varphi(g)$ for
  $\gamma \in G(k)$; (ii) the span of the right translates $\varphi(\cdot\, \kappa)$, $\kappa \in K$, is
  finite-dimensional; (iii) $\varphi$ is annihilated by an ideal of finite codimension of $\mathcal{Z}$; and
  (iv) $\varphi$ has moderate growth: $\lvert \varphi(g) \rvert \le C \lVert g \rVert^{N}$ for some $C$ and
  $N$. They form a space $\mathcal{A}(G)$. If $G = \mathrm{GL}_n$ and
  $\omega$ is a character of the [idele class group](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/adeles-and-ideles/topological-idele-class-group.md),
  $\mathcal{A}(\omega)$ is the subspace of $\varphi$ with $\varphi(zg) = \omega(z)\varphi(g)$ for $z$ in the
  centre $\mathbb{A}^\times$.
- **Constant terms and cusp forms.** For a parabolic subgroup $P = MN$ of $G$ defined over $k$, the
  quotient $N(k) \backslash N(\mathbb{A})$ is compact and the constant term of $\varphi$ along $P$ is
  $\varphi_P(g) = \int_{N(k) \backslash N(\mathbb{A})} \varphi(ng)\, dn$ (probability Haar measure). An
  automorphic form is a cusp form if $\varphi_P = 0$ for every proper parabolic subgroup $P$ of $G$ over
  $k$; for $\mathrm{GL}_n$ it suffices to take the standard maximal parabolic subgroups, of block sizes
  $(n_1, n_2)$, $n_1 + n_2 = n$. The cusp forms form a subspace $\mathcal{A}_0(G)$.
- **Hecke algebra.** The global Hecke algebra is $\mathcal{H} = \bigotimes'_v \mathcal{H}_v$, where for a finite
  place $\mathcal{H}_v = C^\infty_c(G(k_v))$ under convolution, for an infinite place $\mathcal{H}_v$ is the
  convolution algebra of bi-$K_v$-finite distributions on $G(k_v)$ supported in $K_v$: it has no unit when $K_v$ is
  infinite (when $K_v$ is finite, as for $\mathrm{GL}_1(\mathbb{R})$ with $K_v = \{\pm 1\}$, the Dirac measure at $1$ is a unit), it
  contains the algebra $\mathcal{A}(K_v)$ of measures $f(k)\,dk$ with $f$ a $K_v$-finite function on $K_v$, and it is
  $\mathcal{U}(\mathfrak{g}_v) \otimes_{\mathcal{U}(\mathfrak{k}_v)} \mathcal{A}(K_v)$, spanned by the convolutions $D * \xi$ of elements
  $D \in \mathcal{U}(\mathfrak{g}_v)$ with such measures $\xi$ (a single element of $\mathcal{U}(\mathfrak{g}_v)$, like the Dirac
  measure at $1$, is not bi-$K_v$-finite when $K_v$ is infinite). The restricted tensor product is taken
  with respect to the idempotents of the $K_v$, $v < \infty$. It acts on $\mathcal{A}(G)$ by right
  convolution, preserving $\mathcal{A}_0(G)$. A representation of $\mathcal{H}_v$ or $\mathcal{H}$ is admissible
  if every fundamental idempotent has finite-rank image.
- **Automorphic representations.** An automorphic representation of $G(\mathbb{A})$ is an irreducible
  subquotient of the $\mathcal{H}$-module $\mathcal{A}(G)$, and a cuspidal automorphic representation is an
  irreducible $\mathcal{H}$-submodule of $\mathcal{A}_0(G)$. For $\mathrm{GL}_n$ and a unitary $\omega$, the space
  $L^2_0(\omega)$ of measurable cuspidal functions with central character $\omega$ that are square
  integrable on $\mathbb{A}^\times \mathrm{GL}_n(k) \backslash \mathrm{GL}_n(\mathbb{A})$ is a unitary
  representation of $\mathrm{GL}_n(\mathbb{A})$ by right translation.

## Depends on

- [Topological idele class group](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/adeles-and-ideles/topological-idele-class-group.md), on which the central characters $\omega$ are defined
- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for parabolic $k$-subgroups $P = MN$ and, for $\mathrm{GL}_n$, the standard maximal ones
- [Compactness of adelic quotients of unipotent groups](compactness-of-unipotent-adelic-quotients.md), for the compact quotient $N(k) \backslash N(\mathbb{A})$ and its invariant probability measure, which define the constant term $\varphi_P$
- [The Hecke algebra of a real reductive group](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/hecke-algebra-of-a-real-reductive-group.md), for the archimedean Hecke algebras $\mathcal{H}_v$, the action of $\mathcal{U}(\mathfrak{g}_v)$ on them by multipliers, their description through the convolutions $D * \xi$, $\mathcal{U}(\mathfrak{g}_v) \otimes_{\mathcal{U}(\mathfrak{k}_v)} \mathcal{A}(K_v)$, and the idempotents of irreducible $K_v$-types

## Proof depends on

- [Product formula for principal ideles](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/adeles-and-ideles/adelic-norm-principal-embedding.md), for the remark that with the entries of $r(x)$ alone every element of $\mathbb{Q}^\times$ would have height $1$
- [Siegel sets and reduction theory for adelic groups](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/reduction-theory-for-adelic-groups.md), for the compactness of the balls of the two-sided height, which its item on heights states, and for $\lVert xy \rVert \le c \lVert x \rVert \lVert y \rVert$, so that right convolution by compactly supported functions at the finite places preserves moderate growth; changing $r$ changes the height by bounded powers, the entries of $r'(x)$ and $r'(x)^{-1}$ being polynomials in those of $r(x)$ and $r(x)^{-1}$
- [Additive duality of adeles and the volume of A/K](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/additive-duality-of-adeles.md), for the compactness of $k \backslash \mathbb{A}$, from which that of $N(k) \backslash N(\mathbb{A})$ follows along a filtration of $N$ by vector groups
- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for the reduction to standard maximal parabolic subgroups of $\mathrm{GL}_n$: every proper parabolic $k$-subgroup is $\mathrm{GL}_n(k)$-conjugate to a standard one, contained in a standard maximal one $Q$; $\varphi_{\gamma P \gamma^{-1}}(g) = \varphi_P(\gamma^{-1} g)$ for $\gamma \in \mathrm{GL}_n(k)$, and for $P \subseteq Q$ the constant term along $P$ is the constant term of $\varphi_Q$ along $N_P \cap M_Q$, as $N_P = N_Q (N_P \cap M_Q)$, so $\varphi_Q = 0$ implies $\varphi_P = 0$ (Cogdell, Lecture 2, §5)
- [Integration over quotients of locally compact groups](../../../MeasureTheory/haar-measure/integration-over-quotients-of-locally-compact-groups.md), for the iterated integration over $N_P(k) \backslash N_P(\mathbb{A})$ through $N_Q$ and $N_P \cap M_Q$ in the transitivity of constant terms
- [Harish-Chandra's convolution identity and uniform moderate growth](harish-chandra-convolution-identity.md), for the action of the archimedean Hecke algebras on $\mathcal{A}(G)$: the derivatives $D\varphi$ of an automorphic form have moderate growth

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  J. W. Cogdell, H. H. Kim and M. R. Murty, *Lectures on Automorphic L-functions*, Fields Institute
  Monographs 20, American Mathematical Society, 2004, <https://doi.org/10.1090/fim/020>; author's version
  <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 2, §1 (the adelic norm
  $\prod_v \max_{i,j}\{\lvert g_{i,j} \rvert_v, \lvert (g^{-1})_{i,j} \rvert_v\}$, p. 16), §2 and
  Definition 2.2 (automorphic forms on $\mathrm{GL}_n$, $\mathcal{A}(\omega)$), §4 ($L^2(\omega)$), §5 and
  Definition 2.5 with the remark after it (cusp forms; maximal parabolic subgroups suffice); Lecture 3,
  opening ("the results remain true for any reductive algebraic group $G$"), §1.0.1 (the Hecke algebras;
  at an archimedean place $\mathcal{H}_v = \mathcal{U}(\mathfrak{g}_v) \otimes_{\mathcal{U}(\mathfrak{k}_v)} \mathcal{A}(K_v)$, with no identity),
  §1.0.2, Definition 3.1 (admissibility), Definition 3.2 (automorphic representations), §4 (spaces of cusp
  forms are subrepresentations) and the paragraph after Definition 3.6 (cuspidal representations as
  irreducible subrepresentations of $\mathcal{A}_0$).
- A. Borel and H. Jacquet, "Automorphic forms and automorphic representations", in *Automorphic Forms,
  Representations and L-functions*, Proc. Sympos. Pure Math. 33, Part 1, American Mathematical Society,
  1979, 189–202, the general definitions, as cited by Cogdell and by Langlands's supplement
  (<https://sunsite.ubc.ca/DigitalMathArchive/Langlands/pdf/notion-ps.pdf>, footnote on p. 2).
- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §12, (12.1) (cuspidal functions on a general
  group) and §13, before (13.2), the height function for an embedding chosen so that its balls are compact, and
  (13.2)–(13.4).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses these notions for $\mathrm{GL}_n$ over number fields and for unitary groups of CM extensions, in the
  statements of `GlobalTheory.Published.CuspRapidDecay`, `GlobalTheory.Published.HarishChandraFinite` and
  `GlobalTheory.Published.AutomorphicFormsFiniteGL`.
