# A fault-tolerant simulation with only good extended rectangles is exact

Let $C'$ be the [fault-tolerant simulation](fault-tolerant-simulation-and-extended-rectangles.md) of a circuit $C$, with
some arrangement of faults in which every extended rectangle is good. Then, for a circuit $C$ that ends by measuring its outputs, the distribution of the final measurement outcomes of $C'$
equals that of $C$. Proof: create ideal decoders at the measurement locations using their correctness, push them to the
left through every gate and wait ExRec by correctness, and remove them at the preparation locations; what remains is $C$.

## Depends on

- [Fault-tolerant simulation of a circuit and extended rectangles](fault-tolerant-simulation-and-extended-rectangles.md)
- [Correct, good and bad extended rectangles](correct-good-and-bad-extended-rectangles.md)

## Proof depends on

- [Good extended rectangles are correct](good-extended-rectangles-are-correct.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 5.2, Theorem 7.
