# Andreev's function

For $b,m\ge 1$, *Andreev's function* $A_{b,m}$ on $n=2^b+bm$ bits reads a truth table $h\in\{0,1\}^{2^b}$ of a function $h:\{0,1\}^b\to\{0,1\}$ and a matrix $y\in\{0,1\}^{b\times m}$ with $b$ rows of $m$ bits, and outputs

$$
A_{b,m}(h,y)=h\bigl(\oplus(y_1),\dots,\oplus(y_b)\bigr),
$$

where $\oplus(y_i)$ is the parity of row $i$. Usually $b\approx\log_2 n$ and $m\approx n/(2\log_2 n)$, so that both parts have about $n/2$ bits.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [The parity language](../../../../complexity-classes/time-and-space-complexity-classes/parity-dec.md)

## Sources

- A. E. Andreev, "On a Method for Obtaining More Than Quadratic Effective Lower Bounds for the Complexity of π-Schemes", Moscow University Mathematics Bulletin, 1987.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
