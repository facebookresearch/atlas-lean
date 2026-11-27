# Strict expressive gain from one witnessed symmetric choice

For finite inputs in the eight-relation signature (edge and configuration markers, edge and configuration block relations, incidence, and three value relations indexed by $\mathbb F_3$), use closed sentences over hereditarily finite sets with atoms, pairing, union, unique-element extraction, cardinality, comprehension and polynomial-bounded fixed-point iteration. There exists one fixed sentence, with an attached resource polynomial and exactly one syntactic occurrence of witnessed symmetric choice, that evaluates to a Boolean on every finite input. No sentence with zero such occurrences has the same set of inputs evaluating to true, even if the latter sentence is partial.

At the witnessed occurrence start with the empty state. A step selects a member of its definable nonempty choice set and updates the state. Every strictly advancing prefix must stay within the polynomial stage and transitive-closure bounds and permit another step; every first fixed-point path must meet the final stage bound, witness constraints and defined-output condition. At each prior choice set the witnesses, computed from the terminal and current states, are coded input automorphisms fixing the free parameters and all states so far and acting transitively on that choice set. A valid witnessed iteration returns true precisely when all first fixed-point paths return true; failed checks are undefined. The bounds use the nonnegative natural floor of the resource polynomial at the input size.

## Depends on

- Hereditarily finite sets with input automorphism action, mutually recursive closed formulas/terms and the precise partial witnessed-iteration evaluation.

## Proof depends on

- A one-occurrence construction, totality on every finite input, and lower bounds for all zero-occurrence sentences in this particular term language.

## Expansion

Prove the history-witness obligations and resource bounds for the constructed sentence, then compare its true-model set to each base sentence. Do not replace the history-fixing condition by witness transitivity over arbitrary permutations.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WitnessedChoice.lean#L469-L471) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WitnessedChoice.lean).
