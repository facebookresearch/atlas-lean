# Relative consistency of the Partition Principle without Choice

Use the first-order language with equality and membership and full pure-set ZF, including all Separation and Replacement instances. If ZF is syntactically consistent, then so is the theory obtained by adjoining the Partition Principle, Choice for ordinal-indexed families, and the negation of the Axiom of Choice. The Partition Principle says that whenever there is a surjection $X\to Y$ there is an injection $Y\to X$, not necessarily a section. Ordinals and families for restricted Choice are interpreted internally, and ordinary Choice is for all sets of nonempty sets. Syntactic consistency here is no derivation of falsum in any finite variable context.

## Depends on

- First-order set language, the full ZF axiom schemes and their deductive system; the internal PP and restricted-choice sentences.

## Proof depends on

- Relative-consistency construction over an arbitrary consistent ZF, including preservation of ordinal-indexed Choice and a witness against unrestricted Choice.

## Expansion

Compare the comparator’s derivation rules and formulas with the standard first-order interface before using any model-transfer step. Do not strengthen the sole premise to transitive-model existence or an inaccessible cardinal.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PartitionConsistency.lean#L316-L321) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PartitionConsistency.lean).
