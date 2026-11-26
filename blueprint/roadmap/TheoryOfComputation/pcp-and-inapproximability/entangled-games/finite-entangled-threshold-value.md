# Finite entangled games and threshold repetition values

The referee draws a question pair from a probability mass function on a product of nonempty finite sets; both answer alphabets are nonempty and finite. A Boolean predicate of questions and answers determines a win. Players share a unit vector in a tensor product of two finite positive-dimensional complex Hilbert spaces. Each party chooses a POVM based only on its own question; effects are positive semidefinite and sum to the identity. Conditional answer probabilities are the expectations of tensor-product effects in the shared vector. The one-shot value is the supremum of the win probability over such finite strategies.

For $k$ repetitions take the product question law, allow arbitrary joint POVMs on each side indexed by that side's question tuple and returning a full answer tuple, and evaluate coordinate wins using the same predicate. The threshold value is the real supremum of the probability that the number of wins is at least the prescribed real fraction of $k$. The dimension of a joint strategy is not bounded by the dimension of any one-shot strategy.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EntangledGames.lean#L10-L62)
