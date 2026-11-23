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

1. **Fourier expansion** (Piatetski-Shapiro; Shalika). Every cusp form satisfies
   $\varphi(g) = \sum_{\gamma \in N_{n-1}(k) \backslash \mathrm{GL}_{n-1}(k)} W_\varphi\!\left(\begin{pmatrix} \gamma & 0 \\ 0 & 1 \end{pmatrix} g\right)$.
   In particular $\varphi \mapsto W_\varphi$ is injective on cusp forms.
2. **Global uniqueness and genericity.** Let $\pi \simeq \bigotimes'_v \pi_v$ be a
   [cuspidal automorphic representation](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md)
   of $\mathrm{GL}_n(\mathbb{A})$, decomposed by the
   [tensor product theorem](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md). The space of
   Whittaker functionals on $\pi$ is one-dimensional, spanned by $\varphi \mapsto W_\varphi(e)$, and $\pi$ and
   each local component $\pi_v$ are generic.
3. **Factorization.** Fix local Whittaker functionals $\Lambda_v$ (with respect to $\psi_v$) such that, at the
   finite places $v$ outside a finite set $S$ containing the places where $\pi_v$ or $\psi_v$ ramifies,
   $\Lambda_v(\xi_v^\circ) = 1$ for the spherical vectors $\xi_v^\circ$ defining the restricted tensor product (at such
   places a spherical vector has non-zero Whittaker value; at a place where $\psi_v$ is ramified it may have
   value $0$). Then there is a constant $c$ with $W_\varphi(e) = c \prod_v \Lambda_v(\xi_v)$ for every $\varphi \in \pi$
   corresponding to a pure tensor $\otimes_v \xi_v$, and $c \ne 0$; absorbing $c$ into one $\Lambda_v$ with $v \in S$,
   $W_\varphi(g) = \prod_v W_{\xi_v}(g_v)$ with $W_{\xi_v}(g_v) = \Lambda_v(\pi_v(g_v)\xi_v)$.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cusp forms and cuspidal automorphic representations
- [Tensor product theorem for automorphic representations](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the decomposition $\pi \simeq \bigotimes'_v \pi_v$

## Proof depends on

- [Whittaker models and the Gelfand–Kazhdan theorems for GLₙ](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/whittaker-models-for-gl-n.md), for the uniqueness of local Whittaker models at the finite places, which gives the global uniqueness in item 2 and the factorization in item 3
- [Whittaker models for GLₙ over archimedean fields](archimedean-whittaker-models-for-gl-n.md), for the uniqueness of continuous Whittaker functionals at the infinite places

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 4, §1 (the
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
