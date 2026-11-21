# Theta correspondence for unitary dual pairs

This node covers the Weil representation and the theta correspondence, local and global, for
unitary dual pairs, with the Siegel–Weil formula, the doubling method and the Rallis inner product
formula in their convergent ranges. Let $E/F$ be a quadratic extension of local or global fields of
characteristic different from $2$, with quadratic character $\varepsilon_{E/F}$, let $V$ be a
Hermitian space and $W$ a skew-Hermitian space over $E$, and let $\mathbb{W}$ be the symplectic
$F$-space obtained from $V \otimes_E W$, so that $(\mathrm{U}(V), \mathrm{U}(W))$ is a dual pair in
$\mathrm{Sp}(\mathbb{W})$. Fix a nontrivial additive character $\psi$.

- **Stone–von Neumann theorem.** Over a local field, the Heisenberg group of $\mathbb{W}$ has, up to
  isomorphism, a unique irreducible representation on which its centre acts by $\psi$ (smooth
  representations over non-archimedean fields; over archimedean fields the theorem is usually
  stated for unitary representations).
- **Weil representation.** The symplectic group acts on this representation projectively, which
  gives a representation of the metaplectic extension $\mathrm{Mp}(\mathbb{W})$; over a
  non-archimedean field this extension is nontrivial. Over a number field the adelic metaplectic
  extension splits over $\mathrm{Sp}(\mathbb{W})(F)$, and the theta distribution is
  $\mathrm{Sp}(\mathbb{W})(F)$-invariant (Weil).
- **Splitting over unitary groups.** A pair of unitary characters of $E^\times$ (globally, of
  $\mathbb{A}_E^\times / E^\times$) whose restrictions to $F^\times$ are $\varepsilon_{E/F}^{\dim W}$
  and $\varepsilon_{E/F}^{\dim V}$ determines a splitting over $\mathrm{U}(V) \times \mathrm{U}(W)$ of
  the metaplectic extension of $\mathrm{Sp}(\mathbb{W})$ by $\mathbb{C}^1$, and hence a Weil
  representation of $\mathrm{U}(V) \times \mathrm{U}(W)$ (Kudla; Harris–Kudla–Sweet).
- **Local Howe duality.** Let $F$ be non-archimedean and $\pi$ an irreducible smooth representation
  of $\mathrm{U}(W)$. The maximal $\pi$-isotypic quotient of the Weil representation is
  $\pi \otimes \Theta(\pi)$, where $\Theta(\pi)$ has finite length (Kudla); $\Theta(\pi)$ has at most
  one irreducible quotient $\theta(\pi)$, and $\theta(\pi) = \theta(\pi') \ne 0$ implies
  $\pi \cong \pi'$ (Waldspurger for odd residue characteristic; Gan–Takeda in general). For reductive
  dual pairs in a real symplectic group, $\Theta(\pi)$ is finitely generated, admissible and
  quasisimple with a unique irreducible quotient, and the pairs that occur form the graph of a
  bijection (Howe).
- **Global theta lifts.** Over a number field, the integral of the theta function
  $\theta(\varphi)(g, h)$ against a cusp form $f$ on one member of the dual pair is an automorphic
  form on the other member, the theta lift of $f$.
- **Weil's convergence criterion.** Let $W_n$ be a split skew-Hermitian space of dimension $2n$
  and $V$ a Hermitian space of dimension $m$ and Witt index $r$. The theta integral
  $I(\varphi)(g) = \int_{[\mathrm{U}(V)]} \theta(\varphi)(g, h)\, dh$ converges for all Schwartz
  functions $\varphi$ if and only if $r = 0$ or $m - r > n$.
- **Siegel–Weil formula.** If moreover $V$ is anisotropic, the Siegel Eisenstein series
  $E(s, \Phi(\varphi))$ on $\mathrm{U}(W_n)$ attached to $\varphi$ is holomorphic at
  $s_{m,n} = (m - n)/2$, and $E(s_{m,n}, \Phi(\varphi)) = c \cdot I(\varphi)$ with $c = 1$ if $m > n$
  and $c = 2$ if $m \le n$, for the Haar measure giving $[\mathrm{U}(V)]$ volume $1$ (Weil for
  $m > 2n$, Ichino for $n < m \le 2n$, Yamana for $m \le n$).
- **Doubling method** (Piatetski-Shapiro–Rallis). For a skew-Hermitian space $U$ and cusp forms
  $f_1, f_2$ in a cuspidal representation $\pi$ of $\mathrm{U}(U)$, the integral of a Siegel
  Eisenstein series on $\mathrm{U}(U \oplus U^-)$ against $f_1 \otimes f_2$ (twisted by a splitting
  character) converges for $\operatorname{Re}(s) \gg 0$, extends to a meromorphic function, and for
  factorizable data is an Euler product of local zeta integrals of matrix coefficients
  $\int \Phi_v(g_v, 1)\, \langle \pi_v(g_v) f_{1}, f_{2} \rangle\, dg_v$. Siegel Eisenstein series
  have meromorphic continuation.
- **Rallis inner product formula.** Let $U$ have dimension $n$ and $V$ dimension $m$ and Witt index
  $r \le n$, with $n < m \le 2n$, and let $\pi$ be an irreducible cuspidal representation of
  $\mathrm{U}(U)$ whose theta lifts to the smaller spaces of the Witt tower of $V$ vanish, so that its
  lift to $\mathrm{U}(V)$ is cuspidal. Then
  $\langle \theta(\varphi_1, f_1), \theta(\varphi_2, f_2) \rangle = 2 \cdot \operatorname{Val}_{s = s_{m,n}} L(s + \tfrac12, \pi \times \chi_V) \cdot Z^*(s, \varphi_1 \otimes \varphi_2, f_1, f_2)$,
  where $s_{m,n} = (m - n)/2$, $\chi_V$ is the splitting character attached to $V$ and $Z^*$ is the
  normalized doubling zeta integral (Gan–Qiu–Takeda; Rallis for symplectic–orthogonal dual pairs).

Regularized Siegel–Weil formulas outside the convergent range are outside this node.

## Expansion

A good expansion replaces this node by definition pages and statements in the following order,
each citing the source and locator below.

1. Heisenberg groups, the Stone–von Neumann theorem, the metaplectic extension and the Weil
   representation, local and global.
2. Hermitian and skew-Hermitian spaces, unitary dual pairs and the splitting characters.
3. The local theta correspondence and Howe duality; the representations of the local groups are
   under [Reductive groups over local fields and their representations](../reductive-groups-over-local-fields/README.md).
4. Theta functions, global theta lifts of cusp forms and Weil's convergence criterion.
5. Siegel Eisenstein series, the Siegel–Weil formula in the anisotropic case, the doubling method
   and the Rallis inner product formula, which uses the previous items.

## Sources

- S. S. Kudla, "Notes on the local theta correspondence", lecture notes, European School in Group
  Theory, 1996, <https://www.math.toronto.edu/~skudla/castle.pdf>: Chapter I, Theorem 1.1 and
  Remark (i) (Stone–von Neumann), pp. 4–5, §I.5 and Proposition 6.6 (metaplectic extension and its
  nontriviality); Chapter II, §II.2 (Howe duality principle).
- D. Prasad, "A brief survey on the theta correspondence", in *Number Theory (Tiruchirapalli,
  1996)*, Contemp. Math. 210, American Mathematical Society, 1998, 171–193; author's version
  <https://www.math.iitb.ac.in/~dprasad/dp.pdf>: §1, Theorem 1 and the paragraph after it; §5,
  Theorem 7 (due to A. Weil, Acta Math. 111 (1964), 143–211) and the definition of global theta
  lifts.
- M. Harris, S. S. Kudla and W. J. Sweet, "Theta dichotomy for unitary groups", J. Amer. Math. Soc.
  9 (1996), 941–1004,
  <https://www.ams.org/journals/jams/1996-9-04/S0894-0347-96-00198-1/S0894-0347-96-00198-1.pdf>:
  introduction, (0.2)–(0.3) (splitting over unitary groups), §1 (cocycles and splittings), §6,
  (6.12)–(6.13) (local doubling zeta integrals). The splittings are due to S. S. Kudla, "Splitting
  metaplectic covers of dual reductive pairs", Israel J. Math. 87 (1994), 361–401.
- D. Prasad, "Theta correspondence for unitary groups", Pacific J. Math. 194 (2000), 427–438,
  <https://msp.org/pjm/2000/194-2/p11.xhtml>: §1.
- W. T. Gan and S. Takeda, "A proof of the Howe duality conjecture", J. Amer. Math. Soc. 29 (2016),
  473–493, arXiv:1407.1995 (version 4): §1 with Theorems 1.1 and 1.2 (Howe duality; finite length
  by Kudla; Waldspurger's theorem), §2.8 (splitting characters).
- R. Howe, "Transcending classical invariant theory", J. Amer. Math. Soc. 2 (1989), 535–552,
  <https://www.ams.org/journals/jams/1989-02-03/S0894-0347-1989-0985172-6/S0894-0347-1989-0985172-6.pdf>:
  §1, Theorems 1 and 1A.
- W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (the second term identity)
  and the Rallis inner product formula", Invent. Math. 198 (2014), 739–831, arXiv:1207.4709
  (version 3): §2.2 (notation), §3.1 (Weil's convergent range, from A. Weil, Acta Math. 113 (1965),
  1–87), §6.1 (Siegel Eisenstein series), Theorem 7.1 and the paragraph after it (Siegel–Weil
  formula in the anisotropic case; A. Ichino, Math. Z. 255 (2007), 721–729; S. Yamana, Compositio
  Math. 147 (2011), 1003–1021), §§11.2–11.6 (theta lifts, doubling see-saw, doubling zeta integral
  after I. I. Piatetski-Shapiro and S. Rallis, LNM 1254 (1987), Part A), Theorem 11.4 (Rallis inner
  product formula).
- S. Rallis, "Injectivity properties of liftings associated to Weil representations", Compositio
  Math. 52 (1984), 139–169, <http://www.numdam.org/item?id=CM_1984__52_2_139_0>: introduction (the
  inner product formula for symplectic–orthogonal dual pairs).
- Proof of the Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet
  L-functions: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>).
  Statement and proof of the Riemann hypothesis certified by the Lean and Mathlib communities in a
  joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative
  (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); independent checks of
  its five main theorems by A. Sutherland (<https://math.mit.edu/~drew/grh/>). Source mirror:
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
  The library has no licence, so none of its Lean comes into ATLAS; ATLAS has no Lean proof of
  its own. Alpöge's proof uses results of this cluster,
  such as `GlobalTheory.Published.StoneVonNeumann`, `GlobalTheory.Published.WeilRepresentationExists`,
  `GlobalTheory.Published.KudlaSplittingSplitUnitary`, `GlobalTheory.Published.HoweDualityReal`,
  `GlobalTheory.Published.WeilThetaConvergence`, `GlobalTheory.Published.SiegelWeilUnitaryConvergent`,
  `GlobalTheory.Published.DoublingMethodLocalZetaIntegrals` and
  `GlobalTheory.Published.RallisInnerProductConvergent`.
