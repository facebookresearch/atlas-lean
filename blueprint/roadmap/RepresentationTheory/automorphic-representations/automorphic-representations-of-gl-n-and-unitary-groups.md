# Automorphic representations of GLₙ and unitary groups

This node covers automorphic forms and automorphic representations of $\mathrm{GL}_n$ over a number
field $F$ with adele ring $\mathbb{A}$, their cuspidal spectrum and multiplicity one theorems, the
classification of Jacquet and Shalika, the base change from unitary groups to general linear groups,
and Clozel's purity lemma.

- **Automorphic forms.** An automorphic form on $\mathrm{GL}_n(\mathbb{A})$ is a smooth function on
  $\mathrm{GL}_n(F) \backslash \mathrm{GL}_n(\mathbb{A})$ that is right $K$-finite, finite under the
  centre of the enveloping algebra, and of moderate growth; it is a cusp form if its constant terms
  $\int_{U(F) \backslash U(\mathbb{A})} \varphi(ug)\, du$ vanish for the unipotent radicals $U$ of all
  proper parabolic subgroups. An automorphic representation is an irreducible subquotient of the
  space of automorphic forms, as a module for the global Hecke algebra (Borel–Jacquet). For a
  reductive group in general, the automorphic representations are the constituents of
  representations parabolically induced from cuspidal ones (Langlands).
- **Cuspidal spectrum.** Cusp forms are rapidly decreasing modulo the centre on a fundamental
  domain, and for a unitary central character $\omega$ the space $L^2_0(\omega)$ of cusp forms is a
  discrete Hilbert direct sum, with finite multiplicities, of irreducible unitary representations
  (Gelfand–Piatetski-Shapiro). For a fixed $K_\infty$-type, a fixed compact open subgroup of the
  finite-adelic points, a fixed ideal of finite codimension in the centre of the enveloping algebra
  and a fixed central character, the space of automorphic forms is finite-dimensional
  (Harish-Chandra).
- **Tensor product theorem** (Flath). An irreducible admissible representation $\pi$ of the global
  Hecke algebra is a restricted tensor product $\bigotimes'_v \pi_v$ of irreducible admissible
  representations of the local Hecke algebras, where $\pi_v$ has a $K_v$-fixed vector for almost all
  $v$.
- **Multiplicity one.** An irreducible cuspidal representation of $\mathrm{GL}_n(\mathbb{A})$ occurs
  with multiplicity at most one in the space of cusp forms (Piatetski-Shapiro, Shalika). Strong
  multiplicity one: two irreducible cuspidal representations $\pi_1, \pi_2$ with
  $\pi_{1,v} \cong \pi_{2,v}$ for all $v$ outside a finite set $S$ are equal; Piatetski-Shapiro's
  original proof needed $S$ to consist of finite places.
- **Rankin–Selberg $L$-functions and the classification of Jacquet and Shalika.** For unitary
  cuspidal representations $\pi$ of $\mathrm{GL}_n(\mathbb{A})$ and $\pi'$ of
  $\mathrm{GL}_m(\mathbb{A})$ with $m \le n$, the completed Rankin–Selberg $L$-function
  $L(s, \pi \times \pi') = \prod_v L(s, \pi_v \times \pi'_v)$, the product over all places
  including the archimedean ones, extends to a meromorphic function, bounded in vertical strips of
  finite width away from its poles, that satisfies a functional equation. It is entire if $m < n$.
  If $m = n$, its poles are simple and lie at the $s = i\sigma$ and $s = 1 + i\sigma$ with
  $\tilde\pi \cong \pi' \otimes \lvert \det \rvert^{i\sigma}$, and it is entire if there is no such
  $\sigma$; in particular $L(s, \pi \times \tilde\pi)$ has a simple pole at $s = 1$. If constituents
  $\pi$ and $\pi'$ of representations induced from cuspidal representations $\tau_1 \otimes \dots \otimes \tau_r$
  and $\tau'_1 \otimes \dots \otimes \tau'_{r'}$ have isomorphic local components outside a finite
  set of places, then $r = r'$ and the $\tau'_j$ are the $\tau_i$ up to order (Jacquet–Shalika); this
  gives the category of isobaric representations.
- **Unitary groups and base change.** For a quasi-split unitary group $U_{E/F}(N)$ attached to a
  quadratic extension $E/F$, Mok decomposes the discrete automorphic spectrum as a direct sum, over
  square-integrable global parameters $\psi = \mu_1 \boxtimes \nu_1 \boxplus \dots \boxplus \mu_r \boxtimes \nu_r$,
  of the representations $\pi$ in the subsets $\Pi_\psi(\varepsilon_\psi)$ of their global packets cut
  out by a sign character $\varepsilon_\psi$. Here the pairs $(\mu_i, \nu_i)$ are distinct,
  $\mu_i$ is a conjugate self-dual unitary cuspidal automorphic representation of
  $\mathrm{GL}_{m_i}(\mathbb{A}_E)$, $\nu_i$ is the irreducible algebraic representation of
  $\mathrm{SL}_2(\mathbb{C})$ of dimension $d_i$, $\sum_i m_i d_i = N$, and each $\mu_i \boxtimes \nu_i$
  satisfies a parity condition relative to $N$. He deduces the weak base change of discrete
  automorphic representations of $U_{E/F}(N)$ to $\mathrm{GL}_N$ over $E$; his proof relies on the
  stabilization of the twisted trace formula. The node also covers the base change and automorphic
  induction for $\mathrm{GL}_n$ of Arthur and Clozel, along solvable extensions of number fields,
  whose proof reduces to cyclic extensions.
- **Purity** (Clozel). If $\pi$ is a cuspidal algebraic automorphic representation of
  $\mathrm{GL}_n(\mathbb{A}_F)$, there is an integer $w$ such that at every archimedean place $v$ the
  restriction to $\mathbb{C}^\times$ of $\sigma_v \otimes \lvert \cdot \rvert^{(n-1)/2}$, with
  $\sigma_v$ the Langlands parameter of $\pi_v$, is a direct sum of characters
  $z \mapsto z^{p_j} \bar z^{q_j}$ with $p_j + q_j = w$ for all $j$.

Representations of the local groups are described under
[Reductive groups over local fields and their representations](../reductive-groups-over-local-fields/README.md);
the trace formula and the cohomology of arithmetic groups are outside this node.

## Expansion

A good expansion replaces this node by definition pages and statements in the following order,
each citing the source and locator below.

1. Adeles of a number field and the adelic points of $\mathrm{GL}_n$ and of unitary groups, with
   links to [Adeles and class field theory](../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/README.md).
2. Automorphic forms, cusp forms, automorphic representations and the tensor product theorem.
3. Rapid decay of cusp forms, the discreteness of the cuspidal spectrum and Harish-Chandra's
   finiteness theorem.
4. Whittaker–Fourier expansions, multiplicity one and strong multiplicity one.
5. Rankin–Selberg $L$-functions, the classification of Jacquet and Shalika and isobaric
   representations.
6. Unitary groups, their square-integrable global parameters (with Arthur's
   $\mathrm{SL}_2(\mathbb{C})$ factors) and weak base change; cyclic, and then solvable, base change
   and automorphic induction for $\mathrm{GL}_n$.
7. Cuspidal algebraic representations and Clozel's purity lemma.

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  J. W. Cogdell, H. H. Kim and M. R. Murty, *Lectures on Automorphic L-functions*, Fields
  Institute Monographs 20, American Mathematical Society, <https://doi.org/10.1090/fim/020>;
  author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 2,
  Definitions 2.2 and 2.5, Theorems 2.1 (Harish-Chandra) and 2.2 (Gelfand and Piatetski-Shapiro);
  Lecture 3, Definition 3.2, Theorem 3.2 and Corollary 3.2.1 (tensor product theorem), Theorem 3.7;
  Lecture 4, Theorems 4.2 and 4.3 and the remark after Theorem 4.3; Lecture 9, Definition 9.1
  (the global, completed $L$-function) and Theorems 9.1–9.4.
- A. Borel and H. Jacquet, "Automorphic forms and automorphic representations", and R. P.
  Langlands, "On the notion of an automorphic representation. A supplement to the preceding
  paper", Proc. Sympos. Pure Math. 33, Part 1, American Mathematical Society, 1979, 189–202 and
  203–207; Langlands's supplement read in <https://sunsite.ubc.ca/DigitalMathArchive/Langlands/pdf/notion-ps.pdf>:
  Lemma 1, Proposition 2 and the first footnote. The tensor product theorem is due to D. Flath,
  "Decomposition of representations into tensor products", ibid., 179–183.
- H. Jacquet and J. A. Shalika, "On Euler products and the classification of automorphic
  representations I" and "On Euler products and the classification of automorphic forms II", Amer.
  J. Math. 103 (1981), <https://doi.org/10.2307/2374103> and <https://doi.org/10.2307/2374050>.
- C. P. Mok, "Endoscopic classification of representations of quasi-split unitary groups", Mem.
  Amer. Math. Soc. 235 (2015), no. 1108, arXiv:1206.0882 (version 5): introduction, §2.3 (formal
  global parameters $\mu \boxtimes \nu$), Definition 2.4.7 (square-integrable parameters and their
  parity condition), Theorem 2.5.2 (decomposition of the discrete spectrum), §2.6 (the
  stabilization of the twisted trace formula), §4.3 with display (4.3.5) and Corollary 4.3.8 (weak
  base change).
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula*, Annals of Mathematics Studies 120, Princeton University Press, 1989: Chapter 3 "Base
  Change" (pp. 199–224). Their results are summarized in L. Clozel, "Base change for GL(n)",
  Proceedings of the International Congress of Mathematicians (Berkeley, 1986), Vol. 1, American
  Mathematical Society, 1987, 791–797,
  <https://www.mathunion.org/fileadmin/ICM/Proceedings/ICM1986.1/ICM1986.1.ocr.pdf>: §1.4,
  Theorem 1.2 (base change and automorphic induction along solvable extensions) and §2 (the cyclic
  case, to which the proofs reduce).
- L. Clozel, "Motifs et formes automorphes : applications du principe de fonctorialité", in
  *Automorphic Forms, Shimura Varieties, and L-functions*, Vol. I, Perspect. Math. 10, Academic
  Press, 1990, 77–159; the purity lemma as stated in D. Ramakrishnan, "Decomposition and parity of
  p-adic representations attached to algebraic automorphic forms on GL(4)", arXiv:1301.1668
  (version 2), introduction.
- Proof of the Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet
  L-functions: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>).
  Statement and proof of the Riemann hypothesis certified by the Lean and Mathlib communities in a
  joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative
  (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); independent checks of
  its five main theorems by A. Sutherland (<https://math.mit.edu/~drew/grh/>). Source mirror:
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
  The library has no licence, so none of its Lean comes into ATLAS; ATLAS has no Lean proof of
  its own. Related formal statements in Alpöge's proof, often in specialised forms,
  include `GlobalTheory.Published.CuspRapidDecay`, `GlobalTheory.Published.SiegelSetUnitary`,
  `GlobalTheory.Published.HarishChandraFinite`, `GlobalTheory.Published.CuspidalSpectrumGL`,
  `GlobalTheory.Published.FlathFactorisation`, `GlobalTheory.Published.CuspidalMultiplicityOne`,
  `GlobalTheory.Published.JacquetShalika` and `GlobalTheory.Published.ClozelPurity`.
