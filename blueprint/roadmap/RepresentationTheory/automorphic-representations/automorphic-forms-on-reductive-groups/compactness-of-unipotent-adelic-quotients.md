# Compactness of adelic quotients of unipotent groups

This node is still to be broken down. It covers the compactness of the adelic quotients of unipotent
radicals of parabolic subgroups, which the definition of constant terms of automorphic forms uses. Let $k$
be a number field with adele ring $\mathbb{A}$, $\mathbf{G}$ a connected reductive group over $k$ and
$P = MN$ a parabolic $k$-subgroup with unipotent radical $N$.

- **Compactness.** $N(k)$ is a discrete subgroup of $N(\mathbb{A})$ and the quotient
  $N(k) \backslash N(\mathbb{A})$ is compact; it carries a unique $N(\mathbb{A})$-invariant probability
  measure. More generally this holds for every $k$-split unipotent $k$-group.
- **Route.** $N$ has a filtration by normal $k$-subgroups with successive quotients isomorphic to vector
  groups $\mathbb{G}_a^{r}$; for a vector group the statement is the compactness of $k \backslash \mathbb{A}$,
  and the general case follows by induction along the filtration, lifting rational points of each
  quotient and assembling compact fundamental sets.
- **The general linear group.** For $\mathbf{G} = \mathrm{GL}_n$ and a standard parabolic subgroup, $N$ is a
  group of block upper unitriangular matrices, and $N(k) \backslash N(\mathbb{A})$ is a successive extension
  of products of copies of $k \backslash \mathbb{A}$.

A good expansion has pages for the filtration of a $k$-split unipotent group by vector groups, for the
compactness of $N(k) \backslash N(\mathbb{A})$ and for its invariant probability measure, each citing a pinned
source with locators besides the one below.

## Depends on

- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for parabolic subgroups and their unipotent radicals
- [Additive duality of adeles and the volume of A/K](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/additive-duality-of-adeles.md), for the adele ring of $k$ and the discreteness of $k$ in it
- [Integration over quotients of locally compact groups](../../../MeasureTheory/haar-measure/integration-over-quotients-of-locally-compact-groups.md), for the invariant measure on the quotient

## Proof depends on

- [Additive duality of adeles and the volume of A/K](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/additive-duality-of-adeles.md), for the compactness of $k \backslash \mathbb{A}$, the case of a vector group
- Not yet a page: the filtration of a $k$-split unipotent group by normal $k$-subgroups with vector-group quotients, and the surjectivity of $N(\mathbb{A}) \to (N/N')(\mathbb{A})$ on adelic points for such quotients, for the induction

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 2, §5,
  pp. 19–20 ("for any of these unipotent radicals, $U(k) \backslash U(\mathbb{A})$ is compact", for the
  standard parabolic subgroups of $\mathrm{GL}_n$, before Definition 2.5).
