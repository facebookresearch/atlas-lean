# Fault-tolerant preparation gadget

Fix an $[[n, 1, 2t + 1]]$ code. A gadget that prepares an encoded state is *fault tolerant* if it satisfies, for every
number $s \le t$ of faulty locations in it:

- **Prep A:** its output passes the [$s$-filter](r-filter-and-ideal-decoder.md): it is within $s$ errors of a properly
  encoded state;
- **Prep B:** the ideal decoder applied to its output gives the intended unencoded state.

When the preparation gadget appears on both sides of such an equality, the faults are in the same locations and of the same
type.

## Depends on

- [The $r$-filter and the ideal decoder](r-filter-and-ideal-decoder.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)
- [Locations of a quantum circuit](locations-of-a-quantum-circuit.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.2, Definition 3 (properties Prep A and Prep B).
