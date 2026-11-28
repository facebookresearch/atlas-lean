# Existence of the growth limit of a nonnegative bilinear system is undecidable

For bilinear systems with nonnegative coefficients and a nonnegative starting vector, no algorithm decides whether the $n$-th root of the largest entry converges; with a strictly positive vector it always converges.

**Theorem.** In the nonnegative setting, it is undecidable whether, for a [bilinear system](bilinear-systems-and-their-growth-rate.md) $(*,s)$ with nonnegative rational coefficients and a nonnegative rational starting vector, the limit $\lim_{n\to\infty}\sqrt[n]{g(n)}$ exists.

When $s$ is strictly positive the limit always exists, so the undecidability needs zero entries in $s$. This answers a question of Rosenfeld.

## Depends on

- [Bilinear systems and their growth rate](bilinear-systems-and-their-growth-rate.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction is from deciding $\lambda\le1$ in the nonnegative setting, undecidable by Rosenfeld's theorem (Theorem 1 of the source, with a simpler proof there that reduces the joint spectral radius problem). Proposition 1 builds from $(*,s)$ a system $(*',s')$ with $g'(2m)=g(m)$ and $g'(2m+1)=0$, using $s'=(\mathbf 0,1)$ and $(x,i)*'(y,j)=(ijs+x*y,0)$. Adding one coordinate that is always $1$ gives $(*'',s'')$ with $g''(2m+1)=1$ and $g''(2m)=\max\{g(m),1\}$. Then $\liminf\sqrt[n]{g''(n)}=1$ and $\limsup\sqrt[n]{g''(n)}=\max\{\lambda,1\}$, so the limit exists iff $\lambda\le1$.

## Sources

- Vuong Bui, "Growth of bilinear maps III: Decidability", *Theoretical Computer Science* 1056, 2025, article 115515, doi:[10.1016/j.tcs.2025.115515](https://doi.org/10.1016/j.tcs.2025.115515); read in arXiv:2201.09850v3 ([arXiv](https://arxiv.org/abs/2201.09850v3)), whose numbering is used: Theorem 3 and its proof (Section 4), Proposition 1, and Theorem 1 (Rosenfeld's theorem with the source's proof).
