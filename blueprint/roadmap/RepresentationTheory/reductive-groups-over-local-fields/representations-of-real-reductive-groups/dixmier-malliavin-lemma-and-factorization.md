# The Dixmier–Malliavin lemma and factorization along one-parameter subgroups

This node is still to be broken down. It covers the two proof inputs of the
[Dixmier–Malliavin theorem](dixmier-malliavin-theorem.md): a one-dimensional lemma on the Dirac
distribution, and its application along the one-parameter subgroups of a Lie group $G$, separately for
test functions and for vectors of continuous representations on Fréchet spaces.

- **The lemma on $\delta$** (Dixmier–Malliavin, Lemme 2.5; Francis, Theorem 6). For every sequence of
  positive numbers $(c_k)_{k \ge 1}$ there are $f, g \in C_c^\infty(\mathbb{R})$ and scalars $a_k$ with
  $\lvert a_k \rvert \le c_k$ such that the partial sums of $g + \sum_{k \ge 1} a_k f^{(k)}$ converge to
  the Dirac distribution $\delta$ at $0$ in the sense of compactly supported distributions; by rescaling,
  $f$ and $g$ can be chosen supported in any prescribed neighbourhood of $0$. The proof goes through the
  functions on $\mathbb{R}$ whose Fourier transforms are reciprocals of infinite products
  $\prod_i (1 + z^2/\lambda_i^2)$, shown to be Schwartz functions for suitable sequences $(\lambda_i)$.
- **Functions along a flow** (Francis, Theorem 3). If $\mathbb{R}$ acts on a manifold $M$ by the flow of
  a complete vector field $X$ and $\pi(f)\psi(m) = \int_{\mathbb{R}} f(-t)\psi(e^{tX}m)\, dt$, then every
  $\varphi \in C_c^\infty(M)$ is $\pi(f_0)\psi_0 + \pi(f_1)\psi_1$ with $f_i \in C_c^\infty(\mathbb{R})$ supported
  in a prescribed $(-\varepsilon, \varepsilon)$ and $\psi_i \in C_c^\infty(M)$ supported in
  $\operatorname{supp} \varphi$. Iterating along the one-parameter subgroups of a basis of the Lie algebra
  and passing to product coordinates, which turn the resulting products of measures on one-parameter
  subgroups into smooth compactly supported kernels on $G$ with a Jacobian factor, gives the factorization
  of functions in item 1 of the theorem.
- **Vectors.** For a continuous representation of $G$ on a Fréchet space $V$ and $v \in V^\infty$, the
  series $\sum_k a_k X^k v$ converge in the seminorms of $V^\infty$ when the $a_k$ are small enough, and
  the same lemma on $\delta$ writes $v$ as a finite sum of vectors $\pi(f_i)v_i$ (Casselman's exposition,
  Proposition 6.1); this is the vector form, item 2 of the theorem, and is not a consequence of the
  factorization of functions alone.

## Expansion

A good expansion has pages for the Schwartz property of the reciprocal infinite products, for the lemma on
$\delta$ with its support and convergence statements, for the factorization along a flow, for the passage
to kernels on $G$ in product coordinates, and for the vector form with its seminorm estimates, each citing
the sources below with locators.

A good expansion also covers these notions of its own statement:

- a definition page for the flow of a complete vector field on a manifold, which the second item uses in Francis's generality.

It also writes out these steps of its own proof:

- the shift of contour across an unbounded region with the decay estimates of the infinite products that it needs (Casselman, §§2, 4 and 5; Francis, Theorem 6 and the rescaling after it), for the Schwartz property of the reciprocal infinite products.
- the diagonal choice of the coefficients that makes the series converge in each of the countably many seminorms of $V^\infty$ (Casselman, §6), for the vector form.

## Depends on

- [Smooth vectors and K-finite vectors of continuous representations](../../lie-and-topological-representations/smooth-and-k-finite-vectors.md), for smooth vectors and the integrated action $\pi(f)$ in the vector form
- [Vector-valued integrals and distributions on Lie groups](../../lie-and-topological-representations/vector-valued-integrals-and-distributions-on-lie-groups.md), for compactly supported distributions and their weak convergence, for the first item
- [Lie groups: the exponential map, closed subgroups and maximal compact subgroups](../../lie-and-topological-representations/lie-groups-exponential-map-and-maximal-compact-subgroups.md), for one-parameter subgroups and the flows of invariant vector fields, along which the second item is applied

## Proof depends on

- [Fourier transform on the Schwartz space](../../../Analysis/harmonic-analysis/fourier-transform/fourier-transform-clm.md), for the Fourier transform on the Schwartz space of $\mathbb{R}$
- [Fourier inversion formula](../../../Analysis/harmonic-analysis/fourier-transform/fourier-inv-fourier-eq.md), for the identification of the transform of the Schwartz function $\psi$ with the continuous integrable reciprocal product $\chi$ whose inverse transform it is, the two sign conventions differing by a reflection under which these functions are even
- [Lie groups: the exponential map, closed subgroups and maximal compact subgroups](../../lie-and-topological-representations/lie-groups-exponential-map-and-maximal-compact-subgroups.md), for product coordinates of the second kind on a Lie group, $(t_1, \dots, t_d) \mapsto e^{t_1 X_1} \cdots e^{t_d X_d}$, a diffeomorphism near $0$, for the passage to kernels on $G$ with their Jacobian

## Sources

- M. Francis, "A Dixmier-Malliavin theorem for Lie groupoids", arXiv:2009.13760 (version 1): Theorem 1
  (the theorem for Lie groups, "3.1 Théorème, [9]"), Theorem 3 (factorization along a flow), Theorem 6
  ("2.5 Lemme, [9]", the lemma on $\delta$, with the remark on rescaling the supports), the proof of
  Theorem 3, and Lemmas 9–11 and Theorem 12 (the assembly of kernels in product coordinates).
- W. Casselman, "The theorem of Dixmier & Malliavin", *Essays on representations of real groups*,
  University of British Columbia, revised January 24, 2016: Proposition 1.1 and §2,
  Theorem 2.1 and Proposition 2.2 (the infinite products and their Fourier transforms), §4, Lemma 4.1
  (Main Lemma) and Proposition 4.3, §5, Lemma 5.1, and §6, Proposition 6.1 (the vector form).
- J. Dixmier and P. Malliavin, "Factorisations de fonctions et de vecteurs indéfiniment
  différentiables", Bull. Sci. Math. (2) 102 (1978), 307–330: Lemme 2.5, Théorème 3.1 and Théorème 3.3,
  as cited by Francis and by Casselman.
