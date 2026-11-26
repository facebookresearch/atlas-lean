# Values of a hard function on independent samples look random

If no circuit of size $S$ predicts $f:\{0,1\}^n\to\{0,1\}$ with advantage more than $\varepsilon$ (that is, $\Pr_x[g(x)=f(x)]\le\tfrac12+\varepsilon$ for all $g$ of complexity at most $S$), then for independent uniform $x_1,\dots,x_m$ the string $f(x_1)\cdots f(x_m)$ is within statistical distance $\varepsilon m$ of $m$ independent uniform bits.

## Proof sketch

The constant circuits show that $f$ itself is $\varepsilon$-close to a fair coin; statistical distance is subadditive over independent coordinates.

## Depends on

- [Average-case hardness against circuits](average-case-hardness-against-circuits.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
