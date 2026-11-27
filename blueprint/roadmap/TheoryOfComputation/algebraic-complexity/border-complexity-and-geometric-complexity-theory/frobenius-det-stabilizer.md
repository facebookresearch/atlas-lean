# Frobenius: the linear symmetries of the determinant

For $n \ge 2$, a linear map $\phi : \mathbb{C}^{n \times n} \to \mathbb{C}^{n \times n}$ satisfies $\det(\phi(X)) = \det(X)$ for all $X$ if and only if there are $A, B \in \mathrm{GL}_n(\mathbb{C})$ with $\det(AB) = 1$ such that $\phi(X) = AXB$ for all $X$ or $\phi(X) = AX^{\top}B$ for all $X$. Thus the stabilizer of $\det_n$ in $\mathrm{GL}_{n^2}$ is $(\mathrm{SL}_n \times \mathrm{SL}_n)/\mu_n \rtimes \mathbb{Z}_2$ up to the scalars of determinant one, and $\det_n$ is characterized up to scalar by its stabilizer among homogeneous polynomials of degree $n$.

## Proof sketch

A determinant-preserving linear map sends the hypersurface of singular matrices to itself, hence preserves the set of rank-one matrices, the singular locus of highest codimension. Linear maps preserving rank-one matrices are of the form $X \mapsto AXB$ or $X \mapsto AX^{\top}B$ by a classical argument on the two rulings of the Segre variety; comparing determinants gives $\det(AB) = 1$. Characterization by the stabilizer follows from the multiplicity-one decomposition of the invariant polynomials.

## Depends on

- [Determinantal complexity and the padded permanent orbit closure problem](det-vs-perm-gct.md)

## Sources

- G. Frobenius, "Über die Darstellung der endlichen Gruppen durch lineare Substitutionen", Sitzungsberichte der Königlich Preussischen Akademie der Wissenschaften zu Berlin (1897) 994-1015.
- K. D. Mulmuley, M. Sohoni, "Geometric complexity theory I: an approach to the P vs. NP and related problems", SIAM Journal on Computing 31 (2001) 496-526.
