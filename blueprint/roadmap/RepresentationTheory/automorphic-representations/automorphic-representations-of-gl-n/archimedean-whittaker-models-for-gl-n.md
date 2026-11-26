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

## Expansion

A good expansion has pages for the uniqueness of continuous Whittaker functionals, for the Whittaker model
of the contragredient and for the injectivity of the restriction to $P_n$, with the sources below and
J. A. Shalika, "The multiplicity one theorem for $\mathrm{GL}_n$", Ann. of Math. 100 (1974), 171–193, checked
for the exact hypotheses.

A good expansion also writes out these steps of its own proof:

- the anti-automorphism $\sigma(g) = w_n\, {}^t g\, w_n^{-1}$, which preserves $N$ and $\psi$ (transpose-inverse twisted by $w_n$ is an automorphism and sends $\psi$ to $\psi^{-1}$), and the invariance under $\sigma$ of the tempered eigendistributions $f$ with $f(n_1 g n_2) = \psi(n_1) f(g) \psi(n_2)$ (Shalika, 1974), for the uniqueness.
- an independent proof that $\pi$ and $\tilde\pi$ are generic together, through $\tilde\pi \cong \pi \circ \theta$ with $\theta(g) = {}^t g^{-1}$ and the change of variables by $w_n$; the bound on the product alone does not bound either factor when the other could vanish, and with this implication each is at most $1$, for the uniqueness. The isomorphism comes from distribution characters, through the locally integrable functions that represent them, analytic and invariant under conjugation on the regular semisimple set: every matrix is conjugate to its transpose, so there the function $g \mapsto \Theta_\pi({}^t g^{-1})$ of $\pi \circ \theta$ equals $\Theta_\pi(g^{-1})$, that of $\tilde\pi$; the equality holds almost everywhere, hence as distributions by Harish-Chandra's local integrability.
- the determination of an irreducible admissible representation by its distribution character, and the character of the contragredient as $\Theta_\pi(g^{-1})$ (Harish-Chandra), for the same isomorphism; the linked characters node states the existence and regularity of characters, not this separation.
- the Whittaker model of the contragredient (Cogdell, Lecture 4, §2, Remark (iii), p. 32) and the injectivity of the restriction to $P_n$ for generic $\pi$ (Cogdell, Lecture 4, §4, Theorem 4.4, p. 34, after Jacquet and Shalika), each with its own argument.

## Depends on

- [Casselman–Wallach globalization](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/casselman-wallach-globalization.md), for smooth Fréchet representations of moderate growth and their underlying Harish-Chandra modules

## Proof depends on

- [Archimedean Gelfand–Kazhdan criterion](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/archimedean-gelfand-kazhdan-criterion.md), for the uniqueness: if $\sigma$ fixes these eigendistributions, then $\dim \mathrm{Hom}_N(\pi, \psi) \cdot \dim \mathrm{Hom}_N(\tilde\pi, \psi^{-1}) \le 1$ (Sun–Zhu, Theorem 2.3 (a); Cogdell, Lecture 4, §2, Remark (i))
- [Characters, principal series and the Langlands classification for real reductive groups](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/principal-series-of-real-reductive-groups.md), for the distribution characters of admissible representations of finite length, invariant under conjugation, in the proof that $\tilde\pi \cong \pi \circ \theta$

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 4, §2,
  Theorem 4.1 ("due to Gelfand and Kazhdan ($v < \infty$) and Shalika ($v \mid \infty$)", at most one Whittaker
  model), Remarks (i)–(iii) (Bessel distributions; the algebraic functionals, of which only one line extends
  continuously; the contragredient), Definition 4.1, and Theorem 4.4 ("Bernstein and Zelevinsky if $v < \infty$ and Jacquet
  and Shalika if $v \mid \infty$").
- B. Sun and C.-B. Zhu, "A general form of Gelfand–Kazhdan criterion", arXiv:0903.1409 (version 6):
  Theorem 2.3 (a), pp. 5–6 (for closed subgroups $S_1, S_2$ with characters $\chi_1, \chi_2$ and a continuous
  anti-automorphism fixing the relevant tempered eigendistributions,
  $\dim \mathrm{Hom}_{S_1}(U^\infty, \mathbb{C}_{\chi_1}) \dim \mathrm{Hom}_{S_2}(V^\infty, \mathbb{C}_{\chi_2}) \le 1$ for contragredient
  irreducible Casselman–Wallach representations), and Remark 2.4.
