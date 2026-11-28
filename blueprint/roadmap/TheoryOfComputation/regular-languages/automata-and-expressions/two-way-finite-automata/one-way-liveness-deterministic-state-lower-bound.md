# One-way liveness has exponential two-way deterministic state cost

For $h\ge2$, the letters are binary relations on an $h$-element set. A word is live if the ordered relational product is nonempty, with the empty product the identity. Use read-only input bounded by distinct endmarkers, starting on the left marker, with moves left, stay or right and no transitions stepping out from a marker. Acceptance is reaching any head position in an accepting state by a finite run. A single nondeterministic automaton with $h+3$ states and no left moves recognizes the live language both when length-zero runs are allowed and when they are forbidden. Under either respective convention any deterministic $s$-state recognizer satisfies $2^{\lfloor(h-2)/31\rfloor}\le 4(s+b)^2$, with $b=1$ when zero steps are allowed and $b=2$ when a positive run is required.

## Depends on

- Ordered relation product and finite two-way tape computations, with two acceptance conventions.

## Proof outline

Prove the small automaton and deterministic state counting separately, with explicit state overhead for converting between acceptance conventions. Check the empty word and the growing alphabet.

- Same-machine one-way recognition under both conventions and deterministic liveness state lower bound.

## Sources

- [Comparator statement: `OAI.OneWayLiveness.main_theorem`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OneWayLiveness.lean#L95-L102)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/129.md)
