# Whittaker models for GLₙ over archimedean fields

This node is still to be broken down. It covers the archimedean counterparts of the
[non-archimedean theory of Whittaker models](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/whittaker-models-for-gl-n.md)
for $\mathrm{GL}_n(F)$, $F = \mathbb{R}$ or $\mathbb{C}$, that the global theory of $\mathrm{GL}_n$ uses. Let
$N$ be the upper triangular unipotent subgroup, $\psi$ a non-trivial character of $F$, and
$\psi(n) = \psi(n_{12} + \dots + n_{n-1,n})$.

- **Uniqueness** (Shalika). For an irreducible admissible smooth Fréchet representation $\pi$ of
  $\mathrm{GL}_n(F)$ of moderate growth, the space of continuous functionals $\Lambda$ with
  $\Lambda(\pi(n)\xi) = \psi(n)\Lambda(\xi)$ has dimension at most $1$, so $\pi$ has at most one Whittaker
  model $\mathcal{W}(\pi, \psi)$; $\pi$ is generic when the dimension is $1$. The dimension can be $0$: the trivial
  representation of $\mathrm{GL}_n(F)$, $n \ge 2$, has no non-zero functional of this kind, algebraic or continuous.
  For generic $\pi$ exactly one line of the algebraic functionals on the underlying Harish-Chandra module
  extends continuously to $\pi$; the space of algebraic functionals can be larger (for the principal series of
  $\mathrm{GL}_n$, $n \ge 2$, it has dimension $n!$), but need not be (for $n = 1$ both spaces are lines).
- **Contragredient.** If $\pi$ has a Whittaker model, so does $\tilde\pi$, with
  $\mathcal{W}(\tilde\pi, \psi^{-1}) = \{g \mapsto W(w_n\, {}^t g^{-1}) : W \in \mathcal{W}(\pi, \psi)\}$.
- **Kirillov model** (Jacquet–Shalika). The restriction of Whittaker functions to the mirabolic subgroup
  $P_n$ is injective.

A good expansion has pages for the uniqueness of continuous Whittaker functionals, for the Whittaker model
of the contragredient and for the injectivity of the restriction to $P_n$, with the sources below and
J. A. Shalika, "The multiplicity one theorem for $\mathrm{GL}_n$", Ann. of Math. 100 (1974), 171–193, checked
for the exact hypotheses.

## Depends on

- [Casselman–Wallach globalization](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/casselman-wallach-globalization.md), for smooth Fréchet representations of moderate growth and their underlying Harish-Chandra modules

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 4, §2,
  Theorem 4.1 ("due to Gelfand and Kazhdan ($v < \infty$) and Shalika ($v \mid \infty$)", at most one Whittaker
  model), Remarks (i)–(iii) (Bessel distributions; the algebraic functionals, of which only one line extends
  continuously; the contragredient), Definition 4.1, and Theorem 4.4 ("Bernstein and Zelevinsky if $v < \infty$ and Jacquet
  and Shalika if $v \mid \infty$").
