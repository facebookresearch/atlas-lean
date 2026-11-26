# Absolute additive bin packing approximation exists exactly when P equals NP

Use valid raw instances: lists of pairs of natural numbers $(p_i,q_i)$ with $0<p_i\le q_i$, sizes $p_i/q_i$, and unit capacity. The optimum is the least natural bin count for which a feasible assignment exists. The assignment is a list of the same length, each entry a bin index below the reported count, whose bin loads are at most $1$.

There exists an absolute natural constant $c$ and a deterministic polynomial-time finite-stack machine with finite stack alphabets that, on every valid encoded instance, returns a feasible packing with count at most optimum plus $c$, **if and only if** $\mathsf P=\mathsf{NP}$ for the following binary language classes. P consists of language predicates recognized by a finite-alphabet deterministic finite-stack decider with time bounded polynomially in raw bit length. NP uses polynomially bounded binary witnesses and a verifier in that model on input $1^{|x|}0\,x\,w$. The packing algorithm has optional output: a zero bit for absence, and a one bit followed by the binary-framed count and assignment list for a packing. Instances similarly use binary-framed natural pairs and a leading one per list entry followed by a final zero. Its approximation guarantee does not specify behavior on invalid inputs.

## Depends on

- The indexed rational unit-capacity packing model above.

## Proof depends on

- [NP-hardness of each fixed additive bin packing gap](fixed-additive-gap-np-hardness.md) and [conditional exact optimization](exact-bin-packing-from-p-equals-np.md).

## Expansion

Isolate the gap decision threshold test and exact optimizer, and prove closure under polynomial-time bit-transducer composition. Keep the constant independent of the input and the valid-instance guarantee separate from the exact optimizer's malformed-input specification.

## Related topics

- [Feasible bin packing instances](bin-packing-feasible.md) uses integer-list sizes and capacity rather than the rational unit-capacity model.

## Sources

- OpenAI, [binary-witness verifier](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L7-L40), [packings and optimum](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L72-L108), [rational input and output codes](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L208-L307), [class and algorithm definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L313-L335), [third conjunct](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L362).
