# Andreev's formula lower bound n^{5/2 - o(1)}

There is $b_0$ such that for all $b\ge b_0$ and $m\ge\lfloor\log_2 b\rfloor+2$, the De Morgan formula leaf size $L$ of Andreev's function on $2^b+bm$ bits satisfies

$$
2^{2b}m^3\le 144\,b^2\bigl(\lfloor\log_2 b\rfloor+2\bigr)^3L^2 .
$$

With $2^b\approx bm\approx n/2$ this gives $L\ge n^{5/2-o(1)}$.

## Proof sketch

Hard-wire as $h$ a function of $b$ variables with $L(h)>2^b/(3b)$, which exists by counting formulas. Apply to the $bm$ bits of $y$ a random restriction leaving exactly $k=b\,(\lfloor\log_2 b\rfloor+2)\le bm$ of them free. With probability at least $3/4$ the restricted formula has at most $4(k/bm)^{3/2}L$ leaves, and every row keeps a free variable except with probability at most $b\,e^{-(\lfloor\log_2 b\rfloor+2)}<1/4$ (for $b\ge b_0$). For a restriction with both properties, fixing all but one free variable per row leaves $h$ applied to literals, so $2^b/(3b)<L(h)\le 4\bigl((\lfloor\log_2 b\rfloor+2)/m\bigr)^{3/2}L$, which rearranges to the stated inequality. This is the computation of Andreev's argument as presented by Jukna, with the counting bound $2^b/(3b)$ in place of the sharper $2^b/\log_2 b$.

## Depends on

- [Andreev's function](andreev-function.md)

## Proof depends on

- [Subbotovskaya's shrinkage under random restrictions](subbotovskaya-random-restriction-shrinkage.md)
- [Counting functions with small De Morgan circuits](../../circuit-models-and-classes/circuit-models-and-complexity-measures/counting-functions-with-small-circuits.md)

## Sources

- A. E. Andreev, "On a Method for Obtaining More Than Quadratic Effective Lower Bounds for the Complexity of π-Schemes", Moscow University Mathematics Bulletin 42(1), 63–66, 1987.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
