# Fault-tolerant error-correction gadget

Fix an $[[n, 1, 2t + 1]]$ code. An error-correction (EC) gadget is *fault tolerant* if:

- **EC A:** whenever it has at most $s \le t$ faulty locations, its output passes the
  [$s$-filter](r-filter-and-ideal-decoder.md), however many errors the incoming block carries: the output is within $s$
  errors of some codeword, possibly the wrong one;
- **EC B:** whenever the incoming block passes the $r$-filter and the gadget has at most $s$ faulty locations with
  $r + s \le t$, the ideal decoder gives the same result after the gadget as before it: the errors are corrected without
  changing the logical state.

## Depends on

- [The $r$-filter and the ideal decoder](r-filter-and-ideal-decoder.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)
- [Locations of a quantum circuit](locations-of-a-quantum-circuit.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.2, Definition 5 (properties EC A and EC B).
