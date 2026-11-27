# Optimal inner-product approximation with m nonlinear gates

Let $\mathrm{IP}_n(x,y)=\sum_{i=1}^n x_iy_i\bmod 2$. Every circuit over the full binary basis with at most $m$ non-affine gates (affine gates, constants and fan-out free) computes a function $g$ with $\bigl|\mathbb{E}_{x,y}(-1)^{g(x,y)+\mathrm{IP}_n(x,y)}\bigr|\le 2^{m}/2^{n}$, and this is attained for every $m\le n$ by XOR-ing the products on $m$ coordinate pairs. Hence the largest achievable agreement with $\mathrm{IP}_n$ using $m\le n$ non-affine gates is exactly $\tfrac12(1+2^{m-n})$.

## Proof sketch

$(-1)^{\mathrm{IP}_n}$ has all Fourier coefficients of absolute value $2^{-n}$, and the output of a circuit with $m$ non-affine gates has Fourier $\ell_1$-norm at most $2^m$; Parseval-type duality bounds the correlation by the product. For the construction, each untouched pair $x_iy_i$ contributes a factor $\tfrac12$ to the correlation.

## Depends on

- [The Zhegalkin basis and multiplicative complexity](../circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/zhegalkin-basis-and-multiplicative-complexity.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

- [Fourier norm is at most 2^m for circuits with m nonlinear gates](../circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/gate-elimination-and-explicit-lower-bounds/fourier-norm-bounded-by-nonlinear-gates.md)
- [Fourier spectrum of the inner product mod 2](../../../Combinatorics/boolean-functions/fourier-expansion-supplements/fourier-spectrum-of-inner-product-mod-2.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
