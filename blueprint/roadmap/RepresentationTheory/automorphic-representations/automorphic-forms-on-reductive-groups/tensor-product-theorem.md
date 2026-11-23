# Tensor product theorem for automorphic representations

Let $k$, $G$, $K = \prod_v K_v$ and $\mathcal{H} = \bigotimes'_v \mathcal{H}_v$ be as for
[automorphic representations](automorphic-forms-and-automorphic-representations.md), with $K_v$
hyperspecial for almost all finite $v$. If $(\pi_v, V_v)$ is an admissible $\mathcal{H}_v$-module for every
place $v$ and $V_v$ contains a non-zero $K_v$-fixed vector $u_v^\circ$ for almost all finite $v$, the restricted
tensor product $\bigotimes'_v V_v = \varinjlim_S \bigl(\bigotimes_{v \in S} V_v\bigr) \otimes \bigl(\bigotimes_{v \notin S} u_v^\circ\bigr)$
is an $\mathcal{H}$-module $\pi = \bigotimes'_v \pi_v$. It is admissible if every $\pi_v$ is admissible and
$\dim V_v^{K_v} = 1$ for almost all $v$ (which holds when the $\pi_v$ are irreducible), and irreducible if every
$\pi_v$ is irreducible. Without the condition on $\dim V_v^{K_v}$ admissibility fails: with $V_v$ the sum of two
copies of the trivial representation at every finite place, changing the reference vector at one place at a
time gives infinitely many independent vectors fixed by $K_f$.

1. **Flath's decomposition theorem.** Every irreducible admissible $\mathcal{H}$-module $\pi$ is isomorphic
   to $\bigotimes'_v \pi_v$ for irreducible admissible $\mathcal{H}_v$-modules $\pi_v$, almost all of which have a
   non-zero $K_v$-fixed vector.
2. **Automorphic representations.** Every automorphic representation $\pi$ of $G(\mathbb{A})$ decomposes
   as a restricted tensor product $\pi = \bigotimes'_v \pi_v$ of irreducible admissible representations of the
   local Hecke algebras: [smooth representations](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md)
   of $G(k_v)$ at the finite places and [$(\mathfrak{g}_v, K_v)$-modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md)
   at the infinite places, with $\pi_v$ unramified for almost all $v$. The decomposition is abstract: it does
   not factor automorphic forms into functions on the groups $G(k_v)$.
3. **Unitary representations** (Gelfand–Piatetski-Shapiro). Every irreducible unitary representation of
   $G(\mathbb{A})$ on a Hilbert space whose $K$-types have finite multiplicities, in particular every
   irreducible subrepresentation of $L^2_0(\omega)$ for $\mathrm{GL}_n$, and of $L^2_{\mathrm{cusp}}$ when $G(\mathbb{A}) = G(\mathbb{A})^1$
   (as for unitary groups, whose centre is anisotropic), is a restricted Hilbert tensor product
   $\widehat{\bigotimes}'_v \pi_v$ of irreducible unitary representations of the $G(k_v)$: at the finite places
   the smooth vectors of $\pi_v$ form an irreducible admissible representation, and for almost all $v$ the
   space of $K_v$-fixed vectors of $\pi_v$ is a line, containing the distinguished vector of the tensor
   product. The same then holds for any other open compact subgroup $K' = \prod_v K'_v$ of $G(\mathbb{A}_f)$ of product
   form, for instance the stabilizer of a lattice in a faithful representation: $K'_v = K_v$ for almost all $v$,
   since two lattices in a $k$-vector space agree at almost all places, so for each such $K'$ the $K'_v$-fixed
   space is the distinguished line for almost all $v$. For a general $G$, a representation of $G(\mathbb{A})^1$ is
   first extended to $G(\mathbb{A})$ through a character of $A_G(\mathbb{R})^0$. (The finiteness of the $K$-multiplicities is
   part of the hypothesis; for the subrepresentations of the cuspidal spectrum it is supplied by the
   discreteness of the cuspidal spectrum and Harish-Chandra's finiteness theorem.)
4. **Smooth automorphic representations** (Harish-Chandra; Wallach). Let $\mathcal{A}^\infty$ be the space of smooth automorphic
   forms: smooth functions on $G(k) \backslash G(\mathbb{A})$, each fixed by some open compact subgroup of $G(\mathbb{A}_f)$, annihilated by an
   ideal of finite codimension of $\mathcal{Z}$ and of uniform moderate growth, with the limit Fréchet topology of the uniform
   moderate growth seminorms. A smooth automorphic representation $(\pi, V)$ of $G(\mathbb{A})$, a closed irreducible
   subquotient of $\mathcal{A}^\infty$ (for instance the closure in $\mathcal{A}^\infty$ of a cuspidal automorphic representation of $\mathrm{GL}_n$, with any
   central character),
   decomposes as $\pi \simeq \pi_\infty \otimes \pi_f$, where $\pi_\infty = \widehat{\bigotimes}_{v \mid \infty} \pi_v$ is the completed (topological) tensor
   product of irreducible smooth Fréchet representations of moderate growth and $\pi_f = \bigotimes'_{v < \infty} \pi_v$ is the
   restricted tensor product of irreducible admissible smooth representations. The $\mathcal{H}$-module of $K$-finite
   vectors of $V$ is $\bigotimes'_v (\pi_v)_{K_v}$, with $\pi_v$ at an infinite place the Casselman–Wallach completion of its
   Harish-Chandra module.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-and-automorphic-representations.md), for the Hecke algebra $\mathcal{H}$, admissibility and automorphic representations
- [Smooth and admissible representations of p-adic groups](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for the local components at the finite places
- [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for the local components at the infinite places
- [Admissible representations of real reductive groups](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/admissible-representations-of-real-reductive-groups.md), for admissible unitary representations at the infinite places in item 3

## Proof depends on

- [Borel–Casselman theorem on Iwahori-fixed vectors](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/borel-casselman-theorem.md), for the embedding of an irreducible representation with non-zero $K_v$-fixed vectors into an unramified principal series
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the decomposition $G(k_v) = P_0(k_v) K_v$ for a good maximal compact subgroup $K_v$, by which the $K_v$-fixed vectors of an unramified principal series form a line (a fixed vector is determined by its value at $1$), so that, with the embedding above, the $K_v$-fixed vectors of $\pi_v$ form a line for almost all $v$
- [Harish-Chandra's finiteness theorem for automorphic forms](harish-chandra-finiteness-theorem.md), for the admissibility of automorphic representations, which reduces item 2 to item 1, and of the irreducible subrepresentations of $L^2_0(\omega)$ in item 3
- [Admissible representations of real reductive groups](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/admissible-representations-of-real-reductive-groups.md), for the $K$-finite vectors of an admissible representation, which pass from a unitary representation to an admissible $\mathcal{H}$-module and back by completion in item 3
- [Discreteness of the cuspidal spectrum](discreteness-of-the-cuspidal-spectrum.md), for the irreducible subrepresentations of $L^2_{\mathrm{cusp}}$ and their finite $K$-multiplicities in item 3
- [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for the correspondence between closed invariant subspaces of an admissible representation and submodules of its $K$-finite vectors, which makes the $K$-finite vectors of an irreducible admissible unitary representation an irreducible module

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 3, opening ("the
  results remain true for any reductive algebraic group $G$"), §1.0.1 (the restricted tensor product
  $\mathcal{H} = \otimes'_v \mathcal{H}_v$), the paragraph after Definition 3.2 (restricted tensor products of
  admissible representations), Theorem 3.2 (Decomposition Theorem, "a purely algebraic fact about
  $\mathcal{H}$-modules", with D. Flath, "Decomposition of representations into tensor products", Proc.
  Sympos. Pure Math. 33, Part 1, 1979, 179–183, as reference [2]), Corollary 3.2.1 and the note after it
  (the remark after Definition 3.2 that local admissibility gives global admissibility needs the
  one-dimensionality of almost all spherical spaces, as above),
  Lecture 2, Definition 2.3 (smooth automorphic forms, the limit Fréchet topology, density of $\mathcal{A}$ in $\mathcal{A}^\infty$), Lecture 3,
  Theorem 3.3 (Harish-Chandra; Wallach: admissibility of smooth automorphic representations), Definition 3.3
  and Theorem 3.4 (the decomposition theorem for smooth automorphic representations, with the topological
  tensor product at the archimedean places and the Casselman–Wallach completions; item 4), Theorem 3.5
  (Harish-Chandra) and Theorem 3.6 (Gelfand and Piatetski-Shapiro).
- R. P. Langlands, "On the notion of an automorphic representation", Proc. Sympos. Pure Math. 33,
  Part 1, 1979, 203–207,
  <https://sunsite.ubc.ca/DigitalMathArchive/Langlands/pdf/notion-ps.pdf>: the paragraph before Lemma 1
  (the unique unramified constituent $\pi_v^\circ$ of $\mathrm{Ind}\, \sigma_v$ for almost all $v$) and the proof
  of Lemma 1 (the decomposition of a constituent of a restricted tensor product).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a form of item 3 for unitary groups of CM extensions as
  `GlobalTheory.Published.FlathFactorisation`.
