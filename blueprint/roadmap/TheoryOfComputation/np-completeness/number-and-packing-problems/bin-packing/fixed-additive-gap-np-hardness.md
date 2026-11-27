# NP-hardness of each fixed additive bin packing gap

For every natural $c$ and every language $L$ of binary words having a deterministic polynomial-time binary-witness verifier, there is a deterministic polynomial-time finite-stack machine whose stack alphabets are finite. It outputs from each input word a natural $B$ and a list of precisely $5B$ pairs of natural numbers $(p_i,q_i)$, with $0<p_i\le q_i$. The rational sizes $p_i/q_i$ are strictly greater than $1/6$ and at most $1$. If the input is in $L$, the indices can be assigned to $B$ unit-capacity bins; otherwise even $B+c$ bins do not suffice. Each item is assigned once and the sum of sizes in every bin must be at most $1$. The source verifier uses the witness length bound polynomial in the original word length and checks the pair $1^{|x|}0\,x\,w$.

Time is measured in the length of the original word; the output is canonical framed binary $B$ followed by a list of framed binary numerator/denominator pairs. It has a continuation bit for each pair and a terminating zero. The clause makes no LP-value claim on the reduction output, and the non-strict endpoint $a_i\le1$ differs from the strict $a_i<1$ in the existence result for the LP gap.

## Depends on

- The indexed rational unit-capacity packing model above.

## Proof depends on

- An NP-verifier gap reduction proving both the $5B$ item invariant and strict lower bound on sizes throughout the construction, as well as the two feasibility implications.

## Expansion

Give the framed rational packing model and polynomial verifier/encoding bridge. Separate gap soundness from completeness and from the polynomial bit-time implementation rather than translating through a reduction with a different promise or a fixed number of bins.

## Related topics

- [Feasible bin packing instances](bin-packing-feasible.md) uses integer-list sizes and capacity rather than the rational unit-capacity model.

## Sources

- OpenAI, [binary-witness verifier](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L7-L40), [packings and optimum](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L72-L108), [rational input and output codes](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L208-L307), [gap predicate](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L337-L352), [second conjunct](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L361).
