# Matrix multiplication tensor rank is at most twice the multiplication-and-division count

Fix a field $F$ and natural sizes $a,b,c$. Let a finite straight-line program on the formal entries of an $a$-by-$b$ matrix and a $b$-by-$c$ matrix use registers for constants, inputs, sums, differences, products and quotients of earlier registers. Values lie in the fraction field of the polynomial ring in all matrix entries. A division is valid only if its denominator is a nonzero rational function. The specified output register for each product entry must equal its formal polynomial in that fraction field. This is not pointwise agreement on the ground field.

If $g$ is the number of multiplication and division gates together, then the tensor rank over $\overline F$ of the matrix multiplication coefficient tensor for this product is at most $2g$. In the cyclic wire order the tensor is indexed by $[a]\times[b]$, $[b]\times[c]$, $[c]\times[a]$, with coefficient one when their three indices agree cyclically and zero otherwise. Rank is the minimum number of outer products of three vectors summing to this coefficient tensor. The bound counts all product and quotient gates, not only nonscalar ones; it makes no absolute numerical claim such as a ceiling involving $n^{9/4}$ for finite $n$.

## Depends on

- [Tensor rank](tensor-rank.md), the matrix product coefficient tensor, and rational program validity and correctness as defined above.

## Proof depends on

- Formal mixed derivatives of the rational register functions, a shared rank-one span with at most two generators per product or quotient, and specialization of the resulting tensor coefficient equations from the function field to the algebraic closure.

## Expansion

Use mixed derivative identities over any characteristic, solving each quotient relation only with its valid denominator. Preserve the coefficient equations under specialization, including over finite ground fields; no generic ground-field evaluation point is assumed.

## Sources

- OpenAI, [Finite rank and product/quotient bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/CircuitRankSpecialization.lean#L25-L56), [Rational program cost and nonlinear gate count](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/DivisionModel.lean#L20-L45), and [Values, validity and correctness](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/DivisionModel.lean#L63-L119).
