# Andreev's formula lower bound n^{5/2 - o(1)}

There is $b_0$ such that for all $b\ge b_0$ and $m\ge\lfloor\log_2 b\rfloor+2$, the De Morgan formula leaf size $L$ of Andreev's function on $2^b+bm$ bits satisfies

$$
2^{2b}m^3\le 144\,b^2\bigl(\lfloor\log_2 b\rfloor+2\bigr)^3L^2 .
$$

With $2^b\approx bm\approx n/2$ this gives $L\ge n^{5/2-o(1)}$.

## Proof sketch

Hard-wire as $h$ a function of $b$ variables of formula size $\Omega(2^b/\log b)$. A random restriction leaving about $(\log b)$-many variables free in each row of $y$ survives with every row alive with good probability, after which $A_{b,m}$ contains a copy of $h$ on the row parities and needs formula size $\Omega(2^b/\log b)$; Subbotovskaya's shrinkage relates this to $L$ by the factor $(k/n)^{3/2}$.

## Depends on

- [Andreev's function](andreev-function.md)

## Proof depends on

- [Subbotovskaya's shrinkage under random restrictions](subbotovskaya-random-restriction-shrinkage.md)
- [Khrapchenko: parity needs n^2 formula leaves](khrapchenko-parity-needs-n-squared-leaves.md)
- [Counting functions with small De Morgan circuits](../../circuit-models-and-classes/circuit-models-and-complexity-measures/counting-functions-with-small-circuits.md)

## Sources

- A. E. Andreev, "On a Method for Obtaining More Than Quadratic Effective Lower Bounds for the Complexity of π-Schemes", Moscow University Mathematics Bulletin, 1987.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
