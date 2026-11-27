# Uniform characteristic-zero depth-five lower bound for iterated matrix multiplication

The input polynomial is the $(0,0)$ entry of the ordered product of $n$ generic $n\times n$ matrices with independent variables (zero at $n=0$). Circuits consist of scalar or variable leaves and five layers: weighted sums, products, weighted sums, products, and one final weighted sum. Each sum has a common formal input degree even for entries with zero weight; empty sums have degree zero. Product degree is the sum of the formal degrees in its input list, with repetitions counted. Size is the total number of leaves and gates including the output. There is one threshold such that for every characteristic-zero field and every $n$ beyond it, every such circuit computing the input polynomial has size at least $n^{\sqrt n/400}$.

## Depends on

- Formal-degree circuit semantics and ordered multiplication of generic matrices.

## Proof depends on

- [Complex lower bound](imm-complex-depth-five-lower-bound.md) and field transport preserving the finite circuit coefficients, formal degrees and size.

## Expansion

Transport to characteristic zero from finitely generated coefficient fields. The threshold is chosen before the field.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DepthFive.lean#L118-L131) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DepthFive.lean).
