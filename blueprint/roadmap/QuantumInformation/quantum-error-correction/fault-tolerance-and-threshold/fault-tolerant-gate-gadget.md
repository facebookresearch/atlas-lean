# Fault-tolerant gate gadget

Fix an $[[n, 1, 2t + 1]]$ code and a logical gate $U$ on $m$ qubits. A gadget implementing $U$ on $m$ encoded blocks is
*fault tolerant* if, whenever input block $i$ passes an [$r_i$-filter](r-filter-and-ideal-decoder.md) and the gadget has
at most $s$ faulty locations with $s + \sum_i r_i \le t$:

- **Gate A:** every output block passes the $(s + \sum_i r_i)$-filter, so errors may spread between blocks but not grow
  within a block beyond the total number of incoming errors and faults;
- **Gate B:** applying the ideal decoder to each output block gives the same result as applying the ideal decoders to the
  input blocks followed by the ideal gate $U$.

## Depends on

- [The $r$-filter and the ideal decoder](r-filter-and-ideal-decoder.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)
- [Locations of a quantum circuit](locations-of-a-quantum-circuit.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.2, Definition 4 (properties Gate A and Gate B).
