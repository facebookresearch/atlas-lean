# Murty–Kabadi: matrix copositivity is coNP-complete

A symmetric rational matrix $M$ is **copositive** if $x^{\top}Mx\ge0$ for all $x\in\mathbb{R}^{n}_{\ge0}$. Deciding copositivity is $\mathsf{coNP}$-complete, and deciding non-copositivity is $\mathsf{NP}$-complete (under polynomial-time many-one reductions, entries in binary).

## Proof sketch

Membership: if $M$ is not copositive, the minimum of $x^{\top}Mx$ over the standard simplex is negative and is attained at a KKT point, which solves a linear system on its support ($M_Sx_S=\lambda\mathbf 1$, $\mathbf 1^{\top}x_S=1$); such a point is rational with polynomially many bits, and scaling gives a nonnegative integer certificate. Hardness: Murty and Kabadi reduce from subset sum. A short alternative reduction from Clique uses the Motzkin–Straus theorem in the form $\min_{x\in\Delta}x^{\top}(A_{\overline{G}}+I)x=1/\omega(G)$ over the standard simplex $\Delta$: the matrix $k(A_{\overline{G}}+I)-J$ is copositive iff $\omega(G)\le k$ (de Klerk–Pasechnik).

## Depends on

- [The class coNP](../../complexity-classes/the-classes-p-np-and-conp/co-np.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [CLIQUE is NP-complete](../graph-covering-and-domination/clique-independent-set-and-vertex-cover/part-08/clique-dec-np-complete.md)
- [Copositivity has polynomial-size integer certificates of failure](../../../LinearAlgebra/matrix-algebra/linear-inequality-systems-over-ordered-fields/copositivity-failure-certificates.md)

## Sources

- Katta G. Murty and Santosh N. Kabadi, "Some NP-Complete Problems in Quadratic and Nonlinear Programming", Mathematical Programming 39(2), 117–129, 1987.
- T. S. Motzkin and E. G. Straus, "Maxima for Graphs and a New Proof of a Theorem of Turán", Canadian Journal of Mathematics 17, 533–540, 1965.
- E. de Klerk and D. V. Pasechnik, "Approximation of the Stability Number of a Graph via Copositive Programming", SIAM Journal on Optimization 12(4), 875–892, 2002.
- P. J. C. Dickinson and L. Gijben, "On the Computational Complexity of Membership Problems for the Completely Positive Cone and Its Dual", Computational Optimization and Applications 57(2), 403–415, 2014.
