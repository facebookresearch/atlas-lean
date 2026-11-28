# Exact binary rational bin packing conditional on P equals NP

If $\mathsf P=\mathsf{NP}$ for binary languages with finite-alphabet finite-stack polynomial-time deciders and polynomial binary-witness verifiers, then one such polynomial-time machine optimizes rational unit-capacity bin packing. A raw item is a pair of naturals $(p,q)$, valid if $0<p\le q$, and its size is the rational number $p/q$. Encode a natural by its canonical little-endian binary digits with a leading one per digit and a terminating zero. A raw instance is encoded by prefixing each concatenated numerator/denominator pair with a one and terminating the list with a zero; full decoding consumes the whole input. The NP verifier uses the length-delimited word and witness pair, with unary word-length prefix.

On a valid list the machine returns a present result with exactly the minimum bin count and a list of bin indices, one per item, below that count, and with each bin's rational load at most one. On the encoded empty list it returns the present result $(0,[])$. On words failing to decode, and on encodings of lists having at least one invalid pair, it returns no output value (encoded as the single zero bit). A present result has an initial one followed by the encoded count and the encoded list of assignments. The guarantee is one fixed algorithm, with an exact optimum, not merely the length of a certificate.

## Depends on

- The indexed rational unit-capacity packing model above.

## Proof depends on

- Polynomial-time parsing and validation of the raw encoding, a witness verifier for extending partial assignments, and a polynomial-time witness-search and optimum-selection reduction using $\mathsf P=\mathsf{NP}$.

## Expansion

Verify integer arithmetic and bit lengths for checking rational loads. Distinguish an empty valid list from a decoding failure and an invalid decoded input. Prove the search extension queries reproduce a concrete feasible optimum assignment.

## Related topics

- [Feasible bin packing instances](bin-packing-feasible.md) uses integer-list sizes and capacity rather than the rational unit-capacity model.

## Sources

- OpenAI, [BinPackingGap.lean, raw packing and encoding](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L208-L335) and [fourth conjunct of `main_results`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinPackingGap.lean#L363-L372).
