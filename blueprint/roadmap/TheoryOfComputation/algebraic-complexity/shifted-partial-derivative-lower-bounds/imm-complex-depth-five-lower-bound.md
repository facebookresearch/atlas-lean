# Complex depth-five homogeneous lower bound for iterated matrix multiplication

The input polynomial is the $(0,0)$ entry of the ordered product of $n$ generic $n\times n$ matrices with independent variables (zero at $n=0$). Circuits consist of scalar or variable leaves and five layers: weighted sums, products, weighted sums, products, and one final weighted sum. Each sum has a common formal input degree even for entries with zero weight; empty sums have degree zero. Product degree is the sum of the formal degrees in its input list, with repetitions counted. Size is the total number of leaves and gates including the output. Over $\mathbb C$, for all sufficiently large $n$, every such circuit computing the input polynomial has size at least $n^{\sqrt n/400}$.

## Depends on

- Formal-degree circuit semantics and ordered multiplication of generic matrices.

## Proof depends on

- Depth-five homogeneous lower bound for generic matrix products.

## Expansion

Verify the homogeneous gate model and derive the numerical constant with the complex threshold.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DepthFive.lean#L118-L131) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DepthFive.lean).
