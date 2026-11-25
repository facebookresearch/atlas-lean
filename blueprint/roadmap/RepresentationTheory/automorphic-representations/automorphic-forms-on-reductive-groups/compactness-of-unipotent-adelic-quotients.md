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
  and the general case follows by induction along $1 \to N' \to N \to N'' \to 1$: a section $N'' \to N$ that is a
  morphism of varieties over $k$ defined on all of $N''$ (for instance in exponential coordinates) lifts the rational
  and the adelic points of $N''$ and carries compact sets to compact sets, so that compact fundamental sets
  assemble. $N(k) \backslash N(\mathbb{A})$ is then a tower of fibrations with
  compact fibres; it is a homogeneous space, not a group, as $N(k)$ need not be normal in $N(\mathbb{A})$: in the
  $3 \times 3$ upper unitriangular group, conjugating $1 + e_{23}$ by $1 + t e_{12}$, $t \in \mathbb{A} \setminus k$, gives
  $1 + e_{23} + t e_{13} \notin N(k)$.
- **The general linear group.** For $\mathbf{G} = \mathrm{GL}_n$ and a standard parabolic subgroup, $N$ is a
  group of block upper unitriangular matrices, and $N(k) \backslash N(\mathbb{A})$ is a tower of fibrations whose
  fibres are products of copies of $k \backslash \mathbb{A}$.

## Expansion

A good expansion has pages for the filtration of a $k$-split unipotent group by vector groups, for the
compactness of $N(k) \backslash N(\mathbb{A})$ and for its invariant probability measure, each citing a pinned
source with locators besides the one below.

## Depends on

- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for parabolic subgroups and their unipotent radicals
- [Additive duality of adeles and the volume of A/K](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/additive-duality-of-adeles.md), for the adele ring of $k$ and the discreteness of $k$ in it
- [Integration over quotients of locally compact groups](../../../MeasureTheory/haar-measure/integration-over-quotients-of-locally-compact-groups.md), for the invariant measure on the quotient

## Proof depends on

- [Additive duality of adeles and the volume of A/K](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/additive-duality-of-adeles.md), for the compactness of $k \backslash \mathbb{A}$, the case of a vector group
- [Unipotent groups in characteristic zero: central series, exponential map and sections](../../../GroupTheory/linear-groups/unipotent-groups-in-characteristic-zero.md), for the filtration of a unipotent group over the number field $k$ by normal $k$-subgroups with vector-group quotients and, for each step, a section $N'' \to N$ that is a morphism of $k$-varieties defined everywhere, which gives the surjectivity of $N(k) \to N''(k)$ and of $N(\mathbb{A}) \to N''(\mathbb{A})$ and compact lifts of compact sets, for the induction

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 2, §5,
  pp. 19–20 ("for any of these unipotent radicals, $U(k) \backslash U(\mathbb{A})$ is compact", for the
  standard parabolic subgroups of $\mathrm{GL}_n$, before Definition 2.5).
- A. Borel, "Some finiteness properties of adele groups over number fields", Publ. Math. IHÉS 16 (1963),
  5–30, <http://www.numdam.org/item?id=PMIHES_1963__16__5_0>: Lemma 5.5 (unimodularity and the invariant
  measure) and Theorem 5.6, p. 21 ($G_{\mathbb{A}}/G_k$ has finite invariant volume if and only if $X_k(G^\circ) = 1$, and is
  compact if moreover every unipotent element of $G_k$ lies in the radical): both conditions hold for a connected
  unipotent group, which gives the compactness for every unipotent $k$-group directly, by another route than
  the induction above.
