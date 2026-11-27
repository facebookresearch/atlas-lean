# Universality from transversal gates and gauge fixing

There is a quantum code family with fault-tolerant implementations of a gate set universal for quantum computation that
use only transversal gates and fault-tolerant error correction, with no distilled resource states. Paetznick and Reichardt show that triorthogonal
stabilizer codes, such as the $[[15, 1, 3]]$ code obtained from the shortened Reed–Muller codes, admit a transversal
controlled-controlled-$Z$ gate; viewing such a code as a [subsystem code](../subsystem-codes/subsystem-code.md), the
transversal Hadamard maps it to a code with the roles of $X$ and $Z$ gauge operators exchanged, and fault-tolerant error
correction that measures and fixes the gauge qubits returns the state to the original code. Together, transversal CCZ,
transversal Hadamard and gauge-fixing error correction implement the logical gates $H$ and CCZ fault-tolerantly. These are
universal in the computational sense, through the real-amplitude encoding (one extra qubit holds the real and imaginary
parts, so circuits of real gates simulate arbitrary circuits, as in Shi's result that Paetznick and Reichardt cite), but not
dense in the unitary group of the original register: their products are real matrices, which even up to a global phase
cannot approximate $\operatorname{diag}(1, i) \otimes I$. The scheme escapes the
[Eastin–Knill theorem](eastin-knill-theorem.md) because the gauge-fixing step is not a unitary product operator.

## Expansion

A sound expansion adds pages for triorthogonal binary matrices and the codes of Bravyi and Haah; Paetznick and Reichardt's
claim that triorthogonality gives a transversal CCZ (the claim in their main text, with its proof); the $[[15, 1, 3]]$
code as a subsystem code with its gauge group; and the gauge-fixing procedure after transversal Hadamard with its fault
tolerance. Each needs its statement checked against the paper.

## Depends on

- [Subsystem code](../subsystem-codes/subsystem-code.md)
- [Transversal gate](transversal-gate.md)

## Related topics

- [The Eastin–Knill theorem](eastin-knill-theorem.md): the no-go theorem that gauge fixing escapes

## Sources

- A. Paetznick and B. W. Reichardt, *Universal fault-tolerant quantum computation with only transversal gates and error correction*, Phys. Rev. Lett. 111 (2013), 090505, arXiv:1304.3709, abstract and the main text (the paragraphs on triorthogonal codes and the transversal CCZ claim, and on the universal gate set from transversal CCZ, transversal Hadamard and error correction).
