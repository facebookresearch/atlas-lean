# Division preserves the formal square matrix multiplication exponent

For either division convention, call $\tau\in\mathbb R$ admissible over a field $F$ if every $\varepsilon>0$ admits a real $C>0$ such that for every natural $N\ge1$ there is a correct formal program multiplying two $N$-by-$N$ matrices with arithmetic cost at most $CN^{\tau+\varepsilon}$. Inputs and constant registers have zero cost; each binary addition, subtraction, multiplication, or, when allowed, division costs one. In the division-free model the identities hold in the polynomial ring. In the division model the register functions and identities are in its fraction field and every denominator is a nonzero rational function. Neither correctness condition is pointwise evaluation on the field.

Over every field $F$, the real infima of the two admissible sets are equal. This is about the square exponent, not equality of finite-size minimum costs or a rectangular division exponent formula.

## Depends on

- The formal square programs, their rational extension, and the admissible sets defined above.

## Proof depends on

- [Tensor rank from product and quotient gates](matrix-product-rank-bounded-by-product-and-quotient-gates.md), invariance of the square asymptotic rank under scalar extension, and its equality with the appropriate power of the formal arithmetic exponent.

## Expansion

Use the cost-preserving embedding of division-free programs for one inequality. In the other direction apply the finite rank bound over the algebraic closure, take tensor powers and transport the asymptotic rank back to the ground field. Keep the exponent definitions separate from the exact numerical value of the square exponent.

## Related topics

- [Formal square exponent](../arithmetic-circuits-for-matrix-multiplication/formal-square-exponent-nine-fourths.md) is a distinct value statement for the division-free model.

## Sources

- OpenAI, [Division admissibility and embedding](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/DivisionExponent.lean#L19-L36), [Square equality](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/DivisionExponent.lean#L79-L95), and [Division-free comparison exponent](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ArithmeticExponent.lean#L20-L30).
