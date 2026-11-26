# Murty–Kabadi: matrix copositivity is coNP-complete

A symmetric rational matrix $M$ is **copositive** if $x^{\top}Mx\ge0$ for all $x\in\mathbb{R}^{n}_{\ge0}$. Deciding copositivity is $\mathsf{coNP}$-complete, and deciding non-copositivity is $\mathsf{NP}$-complete (under polynomial-time many-one reductions, entries in binary).

## Proof sketch

Membership: if $M$ is not copositive, a violating $x$ can be taken to be a nonnegative integer vector with polynomially many bits (vertex of a polyhedron argument), giving an NP certificate. Hardness: reduce Clique via the Motzkin–Straus theorem: for a graph $G$ and $k$, the matrix $k(A_{\overline{G}}+I)-J$ is copositive iff $\omega(G)\le k$.

## Depends on

- [The class coNP](../../complexity-classes/the-classes-p-np-and-conp/co-np.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [VERTEX-COVER (exact size $k$) is NP-complete](../graph-covering-and-domination/clique-independent-set-and-vertex-cover/part-08/vertex-cover-dec-np-complete.md)

## Sources

- Katta G. Murty and Santosh N. Kabadi, "Some NP-Complete Problems in Quadratic and Nonlinear Programming", Mathematical Programming 39(2), 1987.
