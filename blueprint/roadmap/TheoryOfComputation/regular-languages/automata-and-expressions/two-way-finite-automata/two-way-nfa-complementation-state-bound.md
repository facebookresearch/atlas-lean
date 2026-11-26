# Exponential state cost of complementing two-way NFAs

For each $n\ge4$ there is an $n$-state two-way NFA over all binary relations on an $(n-2)$-element set such that every finite two-way NFA recognizing its complement over that same alphabet has at least $\tfrac12\,2^{\lfloor(n-4)/127\rfloor}-1$ states. Input is read only between distinct markers inclusive, with moves left, stay, right, and configurations must stay on that tape. The run starts on the left marker, and a finite run (possibly of length zero) accepts if its last state is accepting. The complement is among all finite words, including the empty word.

## Depends on

- Finite-word two-way nondeterminism with bounded head positions and exact finite-run language complement.

## Proof outline

Keep the same alphabet for the witness and complement and preserve the natural floors in the bound. Show that enabling transitions that would step off the marked input does not change runs, or restrict such transitions by normalization without adding states.

- Complementation obstruction on the relation alphabet, or projection of the stronger explicit-family bound after the state-preserving bridge.

## Sources

- [Comparator statement: `OAI.TwoWayComplementation.complementation_lower_bound_finite`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TwoWayComplementation.lean#L36-L42)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/129.md)
