# Monotone trial CDFs and reciprocal-tail entropy

A trial function on $[0,1]$ is measurable and nondecreasing with values in $[0,1]$. Its tail integral at $t$ is the real integral of its restriction to $[t,1]$ under uniform interval measure. Embed this tail integral and $1-t$ in the extended nonnegative reals, take their inverses, and use the truncated difference of the two inverses. Integrating that difference on $[0,1]$ and dividing by two defines the extended entropy. For a step trial with positive weights summing to one, the CDF at $t$ is the sum of the weights of the step locations at or below $t$. For a quantile, use the pushforward of the uniform interval law. The trivial trial with zero tail must use the extended inverse and is not silently discarded.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SphericalField.lean#L19-L41)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SphericalField.lean#L241-L266)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SphericalField.lean#L397-L410)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PerceptronFreeEnergy.lean#L46-L62)
