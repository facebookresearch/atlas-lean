# Depth-five homogeneous upper bound for iterated matrix multiplication

The input polynomial is the $(0,0)$ entry of the ordered product of $n$ generic $n\times n$ matrices with independent variables (zero at $n=0$). Circuits consist of scalar or variable leaves and five layers: weighted sums, products, weighted sums, products, and one final weighted sum. Each sum has a common formal input degree even for entries with zero weight; empty sums have degree zero. Product degree is the sum of the formal degrees in its input list, with repetitions counted. Size is the total number of leaves and gates including the output. Over any field and for every $n\ge2$, there is such a circuit computing the input polynomial of size at most $B=2n^3+rn^2+rn^{t+1}+n^{r-1}+1$, where $t=\lceil\sqrt n\rceil$ and $r=\lceil n/t\rceil$. The bound satisfies $B\le n^{\sqrt n+4}$.

## Depends on

- Formal-degree circuit semantics and ordered multiplication of generic matrices.

## Proof depends on

- Block decomposition of the ordered matrix product and the explicit gate-count estimate.

## Expansion

Build the circuit by blocks of at most $t$ matrices, and account for leaves, partial entry sums and final products separately. Prove the displayed bound for all $n\ge2$.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DepthFive.lean#L118-L131) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DepthFive.lean).
