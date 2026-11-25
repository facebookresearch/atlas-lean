# Shintani's formula for spherical Whittaker functions of GLₙ

This node is still to be broken down. It covers the explicit formula for the spherical Whittaker function of an
unramified generic representation of $\mathrm{GL}_n$ over a non-archimedean local field, and the identity of
characters of $\mathrm{GL}_n(\mathbb{C})$ with which the unramified Rankin–Selberg integrals are computed. Let $F$
have ring of integers $\mathcal{O}$, uniformizer $\varpi$ and residue field of order $q$, $K = \mathrm{GL}_n(\mathcal{O})$, $\psi$ an
additive character of conductor zero, trivial on $\mathcal{O}$ but not on $\varpi^{-1}\mathcal{O}$, and $\pi$ an irreducible unramified generic representation of
$\mathrm{GL}_n(F)$ with [Satake parameters](../representations-of-p-adic-reductive-groups/cartan-decomposition-and-satake-isomorphism.md) $A_\pi = \mathrm{diag}(\mu_1(\varpi), \dots, \mu_n(\varpi))$.

- **Shintani's formula** (Shintani; Casselman–Shalika). The $K$-fixed vectors of the
  [Whittaker model](whittaker-models-for-gl-n.md) $\mathcal{W}(\pi, \psi)$ form a line, containing a unique $W^\circ$ with
  $W^\circ(1) = 1$, which satisfies, for
  $\varpi^J = \mathrm{diag}(\varpi^{j_1}, \dots, \varpi^{j_n})$, $W^\circ(\varpi^J) = 0$ unless $j_1 \ge \dots \ge j_n$, and then
  $W^\circ(\varpi^J) = \delta_{B_n}^{1/2}(\varpi^J)\, \chi_J(A_\pi)$, where $\chi_J$ is the character of the irreducible
  representation of $\mathrm{GL}_n(\mathbb{C})$ of highest weight $J$ and $\delta_{B_n}$ the modulus of the upper Borel
  subgroup.
- **Cauchy identity.** For $m \le n$ and $D_n \in \mathrm{GL}_n(\mathbb{C})$, $D_m \in \mathrm{GL}_m(\mathbb{C})$,
  $\sum_{j_1 \ge \dots \ge j_m \ge 0, \ \lvert J \rvert = r} \chi_{(J,0)}(D_n)\, \chi_J(D_m) = \operatorname{tr} S^r(D_n \otimes D_m)$, where
  $(J, 0)$ pads $J$ with zeros and $S^r$ is the $r$-th symmetric power; and
  $\sum_{r \ge 0} \operatorname{tr} S^r(D)\, X^r = \det(1 - XD)^{-1}$.

## Expansion

A good expansion has statement pages for Shintani's formula and for the Cauchy identity in this form, each citing the
sources below with locators. Cogdell derives the formula from the action of the Hecke operators $\Phi_i$ on
$W^\circ(\varpi^J)$, a recursion (Proposition 7.3) solved by the characters $\chi_J$, and the identity from the
decomposition of symmetric powers of a tensor product.

## Depends on

- [Whittaker models and the Gelfand–Kazhdan theorems for GLₙ](whittaker-models-for-gl-n.md), for Whittaker models
- [Cartan decomposition and Satake isomorphism for special maximal compact subgroups](../representations-of-p-adic-reductive-groups/cartan-decomposition-and-satake-isomorphism.md), for the Satake
  parameters

## Proof depends on

- [Cartan decomposition and Satake isomorphism for special maximal compact subgroups](../representations-of-p-adic-reductive-groups/cartan-decomposition-and-satake-isomorphism.md), for the Hecke
  eigenvalues in terms of the Satake parameters

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 7, §1 (the Hecke eigenvalues $q^{i(n-i)/2}\sigma_i(\mu_1(\varpi), \dots, \mu_n(\varpi))$) and §2,
  pp. 55–58 (Proposition 7.3, the recursion; Proposition 7.4, Shintani's formula; the identities for
  $\operatorname{tr}(\rho_{(J,0)}(D_n) \otimes \rho_J(D_m))$ and $\sum_r \operatorname{tr}(S^r(D))X^r$; Proposition 7.5).
- T. Shintani, "On an explicit formula for class-1 'Whittaker functions' on $\mathrm{GL}_n$ over $P$-adic fields", Proc.
  Japan Acad. 52 (1976), 180–182, the original formula, as cited by Cogdell.
- W. Casselman and J. Shalika, "The unramified principal series of p-adic groups II. The Whittaker function",
  Compositio Math. 41 (1980), 207–231, <http://www.numdam.org/item?id=CM_1980__41_2_207_0>, the formula for general
  unramified groups.
