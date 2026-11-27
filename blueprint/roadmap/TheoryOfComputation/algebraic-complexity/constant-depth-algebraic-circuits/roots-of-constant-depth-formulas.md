# Roots of constant product-depth formulas have small formulas

Over a field of characteristic zero, let $P(x,y)\neq0$ be computed by an unbounded fan-in formula $F$ of product-depth $\Delta$, and let $f(x)$ be a polynomial with $P(x,f(x))=0$. Then $f$ has an unbounded fan-in formula of product-depth $\Delta+1$ and size polynomial in the size of $F$ and $\deg f$.

## Proof sketch

For a suitable derivative order $j$ and shift point $x_0$, the polynomial $Q=\partial_y^jP$ shifted by $(x_0,f(x_0))$ has $f$ as a simple root, and Newton iteration truncated at degree $\deg f$ expresses $f$ as a truncated power series in polynomially many derivatives of $Q$; truncation and derivatives are implemented by interpolation at constant product-depth cost.

## Depends on

- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](unbounded-fan-in-formulas-and-product-depth.md)

## Sources

- Somnath Bhattacharjee, Mrinal Kumar, Shanthanu S. Rai et al., "Closure under factorization from a result of Furstenberg", 58th Annual ACM Symposium on Theory of Computing (STOC 2026), 2026.
- Chi-Ning Chou, Mrinal Kumar, Noam Solomon, "Closure Results for Polynomial Factorization", Theory of Computing, 2019.
