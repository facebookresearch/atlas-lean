# Tensor product theorem for automorphic representations

Let $k$, $G$, $K = \prod_v K_v$ and $\mathcal{H} = \bigotimes'_v \mathcal{H}_v$ be as for
[automorphic representations](automorphic-forms-and-automorphic-representations.md), with $K_v$
hyperspecial for almost all finite $v$. If $(\pi_v, V_v)$ is an admissible $\mathcal{H}_v$-module for every
place $v$ and $V_v$ contains a non-zero $K_v$-fixed vector $u_v^\circ$ for almost all finite $v$, the restricted
tensor product $\bigotimes'_v V_v = \varinjlim_S \bigl(\bigotimes_{v \in S} V_v\bigr) \otimes \bigl(\bigotimes_{v \notin S} u_v^\circ\bigr)$
is an $\mathcal{H}$-module $\pi = \bigotimes'_v \pi_v$, admissible if every $\pi_v$ is admissible and irreducible
if every $\pi_v$ is irreducible.

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
   irreducible subrepresentation of $L^2_{\mathrm{cusp}}$ or of $L^2_0(\omega)$, is a restricted Hilbert tensor
   product $\widehat{\bigotimes}'_v \pi_v$ of irreducible unitary representations of the $G(k_v)$, almost all
   unramified.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-and-automorphic-representations.md), for the Hecke algebra $\mathcal{H}$, admissibility and automorphic representations
- [Smooth and admissible representations of p-adic groups](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for the local components at the finite places
- [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for the local components at the infinite places
- [Admissible representations of real reductive groups](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/admissible-representations-of-real-reductive-groups.md), for admissible unitary representations at the infinite places in item 3

## Proof depends on

- [Borel–Casselman theorem on Iwahori-fixed vectors](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/borel-casselman-theorem.md), for the embedding of an irreducible representation with non-zero $K_v$-fixed vectors into an unramified principal series, whose $K_v$-fixed vectors form a line by the Iwasawa decomposition, so that the $K_v$-fixed vectors of $\pi_v$ form a line for almost all $v$
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
  Sympos. Pure Math. 33, Part 1, 1979, 179–183, as reference [2]), Corollary 3.2.1 and the note after it,
  Theorem 3.5 (Harish-Chandra) and Theorem 3.6 (Gelfand and Piatetski-Shapiro).
- R. P. Langlands, "On the notion of an automorphic representation", Proc. Sympos. Pure Math. 33,
  Part 1, 1979, 203–207,
  <https://sunsite.ubc.ca/DigitalMathArchive/Langlands/pdf/notion-ps.pdf>: the paragraph before Lemma 1
  (the unique unramified constituent $\pi_v^\circ$ of $\mathrm{Ind}\, \sigma_v$ for almost all $v$) and the proof
  of Lemma 1 (the decomposition of a constituent of a restricted tensor product).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a form of item 3 for unitary groups of CM extensions as
  `GlobalTheory.Published.FlathFactorisation`.
