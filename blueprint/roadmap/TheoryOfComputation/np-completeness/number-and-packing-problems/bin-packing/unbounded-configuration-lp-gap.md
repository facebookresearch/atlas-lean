# Unbounded additive gap for both bin packing configuration LPs

For every nonnegative integer $c$, there exist a nonnegative integer $B$ and an indexed list $a_0,\ldots,a_{5B-1}$ of rational item sizes, all strictly between $1/6$ and $1$, with both configuration-LP values equal to $B$, but whose minimum integral number of unit-capacity bins is strictly greater than $B+c$. An integral packing into $b$ bins assigns each item index once to one of $b$ bins, and the sum of sizes assigned to each bin is at most $1$.

For the individual-copy LP, use one variable $x_H\ge 0$ for every subset $H$ of the item indices with $\sum_{i\in H}a_i\le 1$, and require $\sum_{H\ni i}x_H\ge 1$ for each index $i$. For the size-type LP, let $S$ be the set of distinct rational sizes occurring in the list and $m_s$ the multiplicity of $s$. Use one variable $y_u\ge 0$ for every vector $u\in\mathbb N^S$ with $\sum_s s u_s\le 1$, and require $\sum_u u_s y_u\ge m_s$ for each $s$. The coordinates $u_s$ are not capped by $m_s$. The two LP values are the infima of $\sum_H x_H$ and $\sum_u y_u$, respectively, over **real** feasible weights, notwithstanding the rational item sizes.

## Depends on

- The indexed rational unit-capacity packing model above.

## Proof depends on

- An instance construction preserving the strict size interval and item count, two real fractional-cover certificates with matching lower bounds, and an integral obstruction above $B+c$.

## Expansion

Separate indexed rational packings from finite individual-copy and type configurations. Define the two real feasible objective sets and their infima, and link the lower-bound certificates and the integral obstruction as proof prerequisites. In particular, do not transfer hardness for the integer binary decision language into an LP gap, or replace real feasibility by rational weights without establishing preservation of the values.

## Related topics

- [Feasible bin packing instances](bin-packing-feasible.md) uses integer-list sizes and capacity rather than the rational unit-capacity model.

## Sources

- OpenAI, [BinPackingGap.lean, indexed packings and LP definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L72-L206) and [first conjunct of `main_results`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L356-L360).
