# Grenet's determinantal representation of the permanent

For every $n\ge1$ and every $n\times n$ matrix $A$ over a commutative ring, $\mathrm{per}(A)=\det G(A)$ for a $(2^n-1)\times(2^n-1)$ matrix $G(A)$ whose entries are entries of $A$, $0$, $1$ or $-1$. Hence $\mathrm{dc}(\mathrm{per}_n)\le 2^n-1$.

## Proof sketch

Take the algebraic branching program on the subsets of $\{1,\dots,n\}$ with an arc from $S$ to $S\cup\{j\}$ ($j\notin S$) of weight $a_{|S|+1,j}$; source-to-sink paths correspond to permutations and have weight $\prod_ia_{i\sigma(i)}$. Identifying the source $\emptyset$ with the sink $\{1,\dots,n\}$ and writing the branching program as a determinant (ones on the diagonal outside the merged source–sink vertex, the sign $(-1)^{n+1}$ absorbed by replacing the diagonal ones on the layer of singletons by $(-1)^{n+1}$) gives size $2^n-1$.

## Depends on

- [Specialization matrices and determinantal representations](specialization-matrices-and-determinantal-representations.md)
- [Permanent of an encoded 0-1 matrix](../../counting-complexity/complexity-of-the-permanent/perm-fun.md)

## Proof depends on

- [Algebraic branching programs as determinants](../../../LinearAlgebra/determinants-and-matrix-identities/determinant-identities-for-complexity/branching-programs-as-determinants.md)

## Sources

- J. M. Landsberg and Nicolas Ressayre, "Permanent v. determinant: an exponential lower bound assuming symmetry and a potential path towards Valiant's conjecture", Computational Complexity 26 (2017), 325–360, Section 2.2 and Proposition 2.9 (arXiv:1508.05788; attributing the $(2^n-1)\times(2^n-1)$ construction to Bruno Grenet, 2011). The construction is a polynomial identity with integer coefficients, so it holds over every commutative ring.
