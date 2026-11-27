# Correct, good and bad extended rectangles

Consider an [extended rectangle](fault-tolerant-simulation-and-extended-rectangles.md) with a given arrangement of faults.
A gate or wait ExRec is *correct* if following it by ideal decoders gives the same result as following its leading EC
steps by ideal decoders and then the ideal gate; a preparation ExRec is correct if the ideal decoder after it gives the
intended state; a measurement ExRec is correct if it gives the same result as its leading EC steps followed by the ideal
decoder and an ideal measurement. An ExRec is *good* if it contains at most $t$ faulty locations and *bad* otherwise.
Within a whole circuit, an ExRec whose trailing EC step is also the leading EC step of a bad ExRec is *truncated*: that
step is removed from it, and good and bad are decided for the truncated ExRec, recursively from the end of the circuit.

## Depends on

- [Fault-tolerant simulation of a circuit and extended rectangles](fault-tolerant-simulation-and-extended-rectangles.md)
- [The $r$-filter and the ideal decoder](r-filter-and-ideal-decoder.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 5.1, Definitions 8 and 9, equations (72)–(74), and Section 5.2, Definition 10.
