# Whether a bilinear system produces the zero vector is undecidable

No algorithm decides, for a bilinear map and starting vector with coefficients and entries of arbitrary signs, whether some combination of copies of the vector equals the zero vector.

**Theorem.** When no sign condition is imposed on the coefficients of $*$ or on the entries of $s$, it is undecidable whether a [bilinear system](bilinear-systems-and-their-growth-rate.md) $(*,s)$ can produce the zero vector, that is, whether some combination of instances of $s$ is $0$. The coefficients $c_{ijk}$ and the entries of $s$ are rational, given as fractions of integers; the reduction below produces integer ones, so the problem is undecidable already for integer inputs.

This answers a question of Rosenfeld.

## Depends on

- [Bilinear systems and their growth rate](bilinear-systems-and-their-growth-rate.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Mortality is undecidable for six 3 × 3 or two 18 × 18 integer matrices](../matrix-mortality-and-freeness/mortality-is-undecidable-for-six-3-3-or-two-18-1.md)

## Expansion

The proof reduces mortality of a pair of matrices $\{A,B\}$, of size $d$: is some product of matrices from $\{A,B\}$ the zero matrix? In $\mathbb R^{d^2+2}$, write vectors as $(C,i,j)$ with $C$ a $d\times d$ matrix, let $s=(\mathbf I,1,0)$ and

$$
(C,i,j)*(C',i',j')=\bigl(CC'+ij'(A-\mathbf I)+ji'(B-\mathbf I),\,0,\,ii'\bigr).
$$

Then $s*s=(\mathbf I,0,1)$, $s*(s*s)=(A,0,0)$ and $(s*s)*s=(B,0,0)$, and for combinations of more than three instances the extra coordinates vanish, so the matrix part is a product of matrices from $\{\mathbf I,A,B\}$. Hence some combination is zero iff the pair is mortal.

## Sources

- Vuong Bui, "Growth of bilinear maps III: Decidability", *Theoretical Computer Science* 1056, 2025, article 115515, doi:[10.1016/j.tcs.2025.115515](https://doi.org/10.1016/j.tcs.2025.115515); read in arXiv:2201.09850v3 ([arXiv](https://arxiv.org/abs/2201.09850v3)), whose numbering is used: Theorem 2 and its proof (Section 3).
