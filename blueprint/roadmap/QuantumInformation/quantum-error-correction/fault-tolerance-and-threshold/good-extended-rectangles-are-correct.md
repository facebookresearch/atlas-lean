# Good extended rectangles are correct

Every good [extended rectangle](correct-good-and-bad-extended-rectangles.md), full or truncated, is correct. For a gate
ExRec with $s_1, s_2, s_3$ faults in the leading EC, the gate gadget and the trailing EC, $s_1 + s_2 + s_3 \le t$, the
proof inserts an $s_1$-filter after the leading EC (property EC A), passes it through the gate gadget as an
$(s_1 + s_2)$-filter (Gate A), moves the ideal decoder through the trailing EC (EC B), and then through the gate gadget
(Gate A and Gate B), where it becomes the ideal gate, and removes the filter again (EC A). Preparation and measurement
ExRecs are handled in the same way; for a truncated ExRec one may insert a fault-free EC step before the ideal decoder.

## Depends on

- [Correct, good and bad extended rectangles](correct-good-and-bad-extended-rectangles.md)

## Proof depends on

- [Fault-tolerant gate gadget](fault-tolerant-gate-gadget.md)
- [Fault-tolerant error-correction gadget](fault-tolerant-error-correction-gadget.md)
- [Fault-tolerant preparation gadget](fault-tolerant-preparation-gadget.md)
- [Fault-tolerant measurement gadget](fault-tolerant-measurement-gadget.md)
- [The $r$-filter and the ideal decoder](r-filter-and-ideal-decoder.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 5.1, Theorem 6 and its proof, equations (75)–(80), and Section 5.2, Lemma 3.
