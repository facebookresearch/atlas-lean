# Bad extended rectangles simulate faulty locations

Let $C'$ be the [fault-tolerant simulation](fault-tolerant-simulation-and-extended-rectangles.md) of a circuit $C$ with a
given arrangement of faults, and classify its extended rectangles as good or bad, full or truncated. Let $\tilde C$ be the
circuit obtained from $C$ by keeping each location whose ExRec is good and replacing each location whose ExRec is bad by an
erroneous operation, controlled by ancilla registers that carry the error syndromes. Then there exist such erroneous
operations, namely those induced by the $*$-decoder (Gottesman's equation (82)), for which $C'$ and $\tilde C$ have the
same output distribution; arbitrary replacements need not reproduce it. The proof uses the *$*$-decoder*, an ideal decoder that keeps the error syndrome in a separate
register and is therefore unitary: every ExRec correct for ideal decoders is correct for $*$-decoders, a good truncated
ExRec is correct for both, and a $*$-decoder pushed through a bad ExRec, leading EC included, turns it into an erroneous
gate on the decoded qubit controlled by the syndrome.

## Depends on

- [Correct, good and bad extended rectangles](correct-good-and-bad-extended-rectangles.md)

## Proof depends on

- [Good extended rectangles are correct](good-extended-rectangles-are-correct.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 5.2, equations (81)–(83), Lemma 2, Lemma 3 and Theorem 8.
