# Andreev's formula lower bound n^{5/2 - o(1)}

Andreev's function, an explicit function computable in polynomial time, requires De Morgan formulas of leaf size $n^{5/2-o(1)}$ on $n$ input bits, for the parameter choice $2^b\approx bm\approx n/2$ (a truth table of $b$ variables and $b$ rows of $m$ bits each).

## Proof sketch

Andreev's argument, based on Subbotovskaya's shrinkage: hard-wire as $h$ a function of $b$ variables with $L(h)>2^b/(3b)$, which exists by counting formulas, and apply a random restriction to the $bm$ bits of $y$. With good probability every row keeps a free variable while the formula shrinks by a factor about $(k/bm)^{3/2}$, where $k$ is the number of free variables; fixing all but one free variable per row leaves $h$ applied to literals, so the shrunken formula has at least $L(h)$ leaves.

Derived here with explicit constants: there is $b_0$ such that for all $b\ge b_0$ and $m\ge\lfloor\log_2 b\rfloor+2$, the leaf size $L$ of Andreev's function on $2^b+bm$ bits satisfies

$$
2^{2b}m^3\le 144\,b^2\bigl(\lfloor\log_2 b\rfloor+2\bigr)^3L^2 .
$$

Leave exactly $k=b\,(\lfloor\log_2 b\rfloor+2)\le bm$ bits of $y$ free. With probability at least $3/4$ the restricted formula has at most $4(k/bm)^{3/2}L$ leaves, and every row keeps a free variable except with probability at most $b\,e^{-(\lfloor\log_2 b\rfloor+2)}<1/4$ (for $b\ge b_0$). For a restriction with both properties, $2^b/(3b)<L(h)\le 4\bigl((\lfloor\log_2 b\rfloor+2)/m\bigr)^{3/2}L$, which rearranges to the displayed inequality.

## Depends on

- [Andreev's function](andreev-function.md)

## Proof depends on

- [Subbotovskaya's shrinkage under random restrictions](subbotovskaya-random-restriction-shrinkage.md)
- [Counting functions with small De Morgan circuits](../../circuit-models-and-classes/circuit-models-and-complexity-measures/counting-functions-with-small-circuits.md)

## Sources

- A. E. Andreev, "On a Method for Obtaining More Than Quadratic Effective Lower Bounds for the Complexity of π-Schemes", Moscow University Mathematics Bulletin 42(1), 63–66, 1987.
- Johan Håstad, "The Shrinkage Exponent of de Morgan Formulas is 2", SIAM Journal on Computing 27(1), 48–64, 1998 (Section 1: Andreev, "based upon Subbotovskaya's result, derived an $n^{2.5-o(1)}$ lower bound on the de Morgan formula size for a function in P").
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
