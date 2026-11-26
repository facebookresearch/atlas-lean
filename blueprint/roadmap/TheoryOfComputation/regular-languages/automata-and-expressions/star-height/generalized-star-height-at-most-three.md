# Generalized star height at most three over a finite alphabet

If $\Sigma$ is a finite alphabet and $L\subseteq\Sigma^*$ is accepted by a deterministic finite automaton over $\Sigma$, there is a generalized regular expression over the same alphabet denoting $L$ whose star height is at most $3$. Empty language, empty word and letters have height zero; union and concatenation take the larger height, complement preserves the height, and Kleene star increases it by one. Complements are relative to $\Sigma^*$. No nonempty-alphabet assumption is made.

## Depends on

- [Bounded generalized star height](has-gen-height-le.md). Regularity means acceptance by a deterministic finite automaton, as stated above.

## Proof approach

The source converts a DFA to a recognizer in a finite monoid and uses its prefix-code construction to synthesize an expression of height at most three. The empty alphabet is handled separately. This is a bound on expressions with complement, not on ordinary regular expressions.

## Sources

- OpenAI, [GeneralizedStarHeight.lean, syntax, denotation, height and `main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GeneralizedStarHeight.lean#L9-L44).
