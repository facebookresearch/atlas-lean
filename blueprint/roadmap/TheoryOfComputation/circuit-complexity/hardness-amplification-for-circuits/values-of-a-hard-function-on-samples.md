# Values of a hard function on independent samples look random

If $S\ge1$ and no circuit of size at most $S$ predicts $f:\{0,1\}^n\to\{0,1\}$ with advantage more than $\varepsilon$ (that is, $\Pr_x[g(x)=f(x)]\le\tfrac12+\varepsilon$ for all $g$ of complexity at most $S$), then for independent uniform $x_1,\dots,x_m$ the string $f(x_1)\cdots f(x_m)$ is within statistical distance $\varepsilon m$ of $m$ independent uniform bits.

## Proof sketch

The constant functions have circuit complexity at most $1\le S$, so they show that $f$ itself is $\varepsilon$-close to a fair coin; statistical distance is subadditive over independent coordinates.

## Depends on

- [Average-case hardness against circuits](average-case-hardness-against-circuits.md)

## Proof depends on

- [Statistical distance of products and with shared public samples](../../../Probability/foundations/statistical-distance-and-couplings/statistical-distance-products-and-shared-samples.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009 (hardness definitions and statistical distance).
