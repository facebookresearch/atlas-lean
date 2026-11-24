# Fourier expansion and global Whittaker models of cusp forms on GLₙ

Let $k$ be a number field, $\psi$ a non-trivial character of $\mathbb{A}/k$, $N_n$ the upper triangular
unipotent subgroup of $\mathrm{GL}_n$, and $\psi(u) = \psi(u_{12} + u_{23} + \dots + u_{n-1,n})$ for
$u \in N_n(\mathbb{A})$. For a cusp form $\varphi$ on $\mathrm{GL}_n(\mathbb{A})$, smooth or $K$-finite, its
$\psi$-Whittaker function is

$$W_\varphi(g) = \int_{N_n(k) \backslash N_n(\mathbb{A})} \varphi(ug)\, \psi^{-1}(u)\, du,$$

with $du$ the Haar measure giving the compact quotient $N_n(k) \backslash N_n(\mathbb{A})$ volume $1$ (the
normalization for which the Fourier expansion below has coefficients $1$),

and $W_\varphi$ satisfies $W_\varphi(ug) = \psi(u) W_\varphi(g)$ for $u \in N_n(\mathbb{A})$. A representation $\pi_v$ of
$\mathrm{GL}_n(k_v)$ is generic if it has a non-zero continuous functional $\Lambda_v$ with
$\Lambda_v(\pi_v(u)\xi) = \psi_v(u)\Lambda_v(\xi)$ for $u \in N_n(k_v)$.

1. **Fourier expansion** (Piatetski-Shapiro; Shalika). For $n \ge 2$, every cusp form satisfies
   $\varphi(g) = \sum_{\gamma \in N_{n-1}(k) \backslash \mathrm{GL}_{n-1}(k)} W_\varphi\!\left(\begin{pmatrix} \gamma & 0 \\ 0 & 1 \end{pmatrix} g\right)$.
   In particular $\varphi \mapsto W_\varphi$ is injective on cusp forms.
2. **Global uniqueness and genericity.** Let $\pi \simeq \bigotimes'_v \pi_v$ be a
   [cuspidal automorphic representation](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md)
   of $\mathrm{GL}_n(\mathbb{A})$, decomposed by the
   [tensor product theorem](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md). The space of
   Whittaker functionals on $\pi$ is one-dimensional, spanned by $\varphi \mapsto W_\varphi(e)$, and $\pi$ and
   each local component $\pi_v$ are generic.
3. **Factorization.** Let $S$ be a finite set of places containing the archimedean places and the places
   where $\pi_v$ or $\psi_v$ ramifies (it may be enlarged). Fix non-zero local Whittaker functionals $\Lambda_v$ (with
   respect to $\psi_v$) at every place, such that $\Lambda_v(\xi_v^\circ) = 1$ at the places $v \notin S$ for the spherical vectors
   $\xi_v^\circ$ defining the restricted tensor product (at such places a spherical vector has non-zero Whittaker value;
   at a place where $\psi_v$ is ramified it may have value $0$). Then there is a constant $c \ne 0$ with
   $W_\varphi(e) = c \prod_v \Lambda_v(\xi_v)$ for every $\varphi \in \pi$ corresponding to a pure tensor $\otimes_v \xi_v$; absorbing $c$ into
   $\Lambda_v$ for one $v \in S$, $W_\varphi(g) = \prod_v W_{\xi_v}(g_v)$ with $W_{\xi_v}(g_v) = \Lambda_v(\pi_v(g_v)\xi_v)$. This is a statement on the
   smooth realization $V^\infty$ of $\pi$: the closure of $\pi$ in the space $\mathcal{A}^\infty_0$ of smooth cusp forms (smooth functions on
   $\mathrm{GL}_n(k) \backslash \mathrm{GL}_n(\mathbb{A})$, each fixed by some open compact subgroup of $\mathrm{GL}_n(\mathbb{A}_f)$, annihilated by an ideal of finite
   codimension of $\mathcal{Z}$ and of uniform moderate growth, with the limit Fréchet topology of the uniform moderate growth
   seminorms), a smooth automorphic representation; this needs no unitarity of the central character (for
   unitary $\omega$ it is the space of smooth vectors of the closure of $\pi$ in $L^2_0(\omega)$). By item 4 of the tensor product
   theorem, $V^\infty$ is the completed tensor product of the smooth Fréchet representations $\pi_v$ at the archimedean places
   (the Casselman–Wallach globalizations, on which $N_n(k_v)$ acts) with the restricted tensor product at the finite
   places. The global functional $\varphi \mapsto W_\varphi(e)$ is continuous on $V^\infty$: on the subspace of a given level and moderate-growth
   stage it is bounded by the supremum of $\lvert \varphi \rvert$ over a compact set of representatives of $N_n(k) \backslash N_n(\mathbb{A})$, a continuous
   seminorm there; so it is determined by its values on pure tensors, and the formula for $K$-finite $\varphi$ is its
   restriction.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cusp forms and cuspidal automorphic representations
- [Tensor product theorem for automorphic representations](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the decomposition $\pi \simeq \bigotimes'_v \pi_v$ and, for item 3, the decomposition of the smooth realization (its item 4)

## Proof depends on

- [Whittaker models and the Gelfand–Kazhdan theorems for GLₙ](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/whittaker-models-for-gl-n.md), for the uniqueness of local Whittaker models at the finite places, which gives the global uniqueness in item 2 and the factorization in item 3
- [Whittaker models for GLₙ over archimedean fields](archimedean-whittaker-models-for-gl-n.md), for the uniqueness of continuous Whittaker functionals at the infinite places
- [Additive duality of adeles and the volume of A/K](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/additive-duality-of-adeles.md), for Fourier inversion on the compact groups $k \backslash \mathbb{A}$ and their finite powers, applied to the smooth functions of finite level obtained by restricting a cusp form to successive abelian quotients (item 1)

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 3, §2, Definition 3.3
  and Theorem 3.4 (the smooth representation, a topological tensor product of smooth Fréchet representations
  at the infinite places); Lecture 4, §1 (the
  Whittaker function $W_\varphi$ and the Fourier expansion for $\mathrm{GL}_n$, "recognized independently by
  Piatetski-Shapiro and Shalika", with the induction on the last column), §2 (Whittaker models, $\varphi$
  recovered from $W_\varphi$, Whittaker functionals, Definition 4.1, the compatible local functionals with
  $\Lambda_v(\xi_v^\circ) = 1$), Corollary 4.1.1 (global uniqueness), Corollary 4.1.2 (genericity of $\pi$ and of
  each $\pi_v$) and Corollary 4.1.3 (factorization of Whittaker functions); the normalization at the
  unramified places is that of the unramified Whittaker function, Lecture 7, §2, which assumes $\psi_v$
  unramified.
- B. Poonen, *Tate's thesis*, lecture notes for MIT 18.786 (Spring 2015), PDF of 2025-10-11,
  <https://math.mit.edu/~poonen/786/notes.pdf>: §5.4 (Fourier analysis on the compact group $\mathbb{A}/k$, which
  gives the expansion on each abelian quotient in the induction).
