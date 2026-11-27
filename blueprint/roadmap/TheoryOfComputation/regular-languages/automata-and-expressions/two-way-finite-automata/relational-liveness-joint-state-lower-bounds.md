# Joint two-way complementation and determinization bounds for relational liveness

For every $n\ge4$ there is an $n$-state read-only two-way NFA on the alphabet of all relations on an $(n-2)$-element set that accepts exactly the words with nonempty ordered relation product (empty product identity). Use the two-marker finite-run model of the [complementation bound](two-way-nfa-complementation-state-bound.md), with length-zero acceptance allowed. Every finite two-way NFA for the complement of this same language uses at least $\tfrac12\,2^{\lfloor(n-4)/127\rfloor}-1$ states. If $n\ge131$, every such automaton for the original language with at most one next-state/move pair for every state and scanned symbol uses at least $\tfrac12\,2^{\lfloor(n-4)/127\rfloor}$ states.

## Depends on

- Ordered relation product, and finite marked-input two-way automata with partial deterministic transitions.

## Proof depends on

- Explicit small recognizer and two lower bounds for that one recognized language.

## Expansion

Give the recognizer, then the complement obstruction, then the deterministic bound; connect exact language equality, and show the construction and lower bounds preserve the state count under any native automata adapter. Do not fix the alphabet size as n varies.

## Sources

- [Comparator statement: `OAI.TwoWayComplementation.explicit_family_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TwoWayDeterminization.lean#L57-L70)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/129.md)
