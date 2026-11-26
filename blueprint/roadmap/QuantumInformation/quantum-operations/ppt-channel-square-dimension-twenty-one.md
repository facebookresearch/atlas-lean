# A trace-preserving PPT channel whose square is not entanglement breaking

There exists a complex-linear $\Theta:M_{21}(\mathbb C)\to M_{21}(\mathbb C)$ preserving the trace on every matrix such that $\Theta$ and its composition with output transpose are completely positive. Complete positivity requires sending every positive semidefinite block matrix to a positive semidefinite output after applying the map to each block, for every finite auxiliary index set. But $\Theta\circ\Theta$ is not entanglement breaking: it does not both satisfy complete positivity and send every positive semidefinite amplified input to a finite sum of tensors of positive semidefinite matrices. Trace preservation is for the ordinary unnormalized matrix trace on both source and target.

## Depends on
The finite completely positive, trace-preserving, PPT and separable-output conventions above.

## Proof depends on
- [Dimension-ten PPT pair](ppt-composition-dimension-ten.md), as the non-entanglement-breaking composite used by the channel completion.

## Proof strategy
Build the block channel completion and check the dimension count $10+10+1$, trace on every block, and complete positivity before and after output transpose. Isolate the restriction of its square to the original composite and prove that entanglement breaking would descend to that restriction.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DimensionTenChannel.lean#L44-L50) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/272.md).
