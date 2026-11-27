# The permanent is in VNP via Ryser's formula

Over every commutative ring $K$, the permanent family $\mathrm{per}_n=\sum_{\sigma\in S_n}\prod_i x_{i\sigma(i)}$ is in $\mathsf{VNP}_K$: with Boolean selectors $y_1,\dots,y_n$,

$$
\mathrm{per}_n(x)=\sum_{y\in\{0,1\}^n}\prod_{j=1}^n(2y_j-1)\prod_{i=1}^n\sum_{j=1}^n y_jx_{ij},
$$

and the summand has degree at most $3n$ and an arithmetic circuit with $O(n^2)$ gates, so $(\mathrm{per}_n)\in\mathsf{VNP}_K$ with $m(n)=n$ selectors.

## Proof sketch

Expanding $\prod_i\sum_jy_jx_{ij}$ gives, for each map $\phi:[n]\to[n]$, the monomial $\prod_ix_{i\phi(i)}$ times $\prod_{j\in\mathrm{im}\phi}y_j$; summing with the signs $\prod_j(2y_j-1)$ over $y$ kills every non-surjective $\phi$ by inclusion–exclusion (Ryser's formula: the signs are $(-1)^{n-|S|}$ for the support $S$ of $y$) and leaves each permutation with coefficient one.

## Depends on

- [Valiant's class VNP (p-definable families)](valiants-class-vnp.md)
- [Permanent of an encoded 0-1 matrix](../../counting-complexity/complexity-of-the-permanent/perm-fun.md)

## Proof depends on

- [VP is contained in VNP, and VNP is closed under p-projections](vp-subset-vnp.md)

## Sources

- Herbert J. Ryser, "Combinatorial Mathematics", Carus Mathematical Monographs 14, Mathematical Association of America, 1963 (Ryser's formula).
- Peter Bürgisser, "Completeness and Reduction in Algebraic Complexity Theory", Springer, 2000.
