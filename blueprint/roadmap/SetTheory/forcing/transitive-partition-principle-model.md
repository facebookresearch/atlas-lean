# A transitive model of the Partition Principle without Choice

Let $M$ be an externally countable transitive collection of elements of the ambient ZF set universe (not a code for a set required to belong to that universe). Its membership structure satisfies Pairing, Union, Power Set, full Separation and Collection, Infinity and Choice. Suppose $K\in M$ is a transitive well-ordered cardinal in the ground sense: no ground-coded injection sends it into a smaller ordinal, it does not embed into $\omega$ by a ground function, no ground function from an ordinal below $K$ is cofinal in it, and for each ground cardinal $\kappa<K$ the ground power set of $\kappa$ embeds by a ground function into an ordinal below $K$. Then there is a transitive collection $N$ containing $M$ pointwise, realizing ZF including its schemas, in which every surjection $X\to Y$ implies some injection $Y\to X$, but Choice fails. In the conclusion all sets/functions in those sentences are interpreted in $N$; no ordinal-indexed Choice clause is asserted.

## Depends on

- Transitive ground membership structures, satisfaction and axiom schemas, and ground-coded functions defining inaccessibility.

## Proof depends on

- Construction of the transitive extension with pure ZF, verification of PP, and a family without a choice function.

## Expansion

Formalize the internal/external distinction for each cardinal clause and ensure the new model is a transitive set containing the ground itself pointwise. Prove the failure of Choice separately from the existence of reverse injections.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PartitionPrinciple.lean#L262-L274) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PartitionPrinciple.lean).
