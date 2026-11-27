# Fault-tolerant measurement gadget

Fix an $[[n, 1, 2t + 1]]$ code. A measurement gadget for the code, a circuit that measures an encoded block and outputs a
classical bit, is *fault tolerant* if, whenever the incoming block passes an [$r$-filter](r-filter-and-ideal-decoder.md)
and the gadget has at most $s$ faulty locations with $r + s \le t$, it gives the same result as applying the ideal decoder
and then measuring the decoded qubit: the same outcome probabilities, and the same relative state of the rest of the
computer conditioned on each outcome.

## Depends on

- [The $r$-filter and the ideal decoder](r-filter-and-ideal-decoder.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)
- [Locations of a quantum circuit](locations-of-a-quantum-circuit.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.2, Definition 2 (property Meas).
