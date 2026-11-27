# Fault-tolerant simulation of a circuit and extended rectangles

Let $C$ be a quantum circuit with [locations](locations-of-a-quantum-circuit.md) $C_i$ and fix an $[[n, 1, 2t + 1]]$
code. The *fault-tolerant simulation* $C'$ of $C$ replaces each location $C_i$ by a fault-tolerant gadget for it
([preparation](fault-tolerant-preparation-gadget.md), [measurement](fault-tolerant-measurement-gadget.md),
[gate](fault-tolerant-gate-gadget.md) or wait gadget) and inserts a
[fault-tolerant EC gadget](fault-tolerant-error-correction-gadget.md) between every two consecutive locations. An
*extended rectangle* (ExRec) of $C'$ consists of the gadget for one location $C_i$ together with the EC gadgets between
$C_i$ and its adjacent locations: the *leading* EC steps before it and the *trailing* EC steps after it. A preparation
ExRec has one trailing EC step, a measurement ExRec one leading EC step, and a gate or wait ExRec one leading and one
trailing EC step per block involved. Adjacent ExRecs overlap in a shared EC step.

## Depends on

- [Locations of a quantum circuit](locations-of-a-quantum-circuit.md)
- [Fault-tolerant preparation gadget](fault-tolerant-preparation-gadget.md)
- [Fault-tolerant measurement gadget](fault-tolerant-measurement-gadget.md)
- [Fault-tolerant gate gadget](fault-tolerant-gate-gadget.md)
- [Fault-tolerant error-correction gadget](fault-tolerant-error-correction-gadget.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 5.1, Definitions 6 and 7 and Figure 7.
