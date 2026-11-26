# The phase-flip code corrects any single phase flip

On the [three-qubit phase-flip code](three-qubit-phase-flip-code.md), the four errors $I, Z_1, Z_2, Z_3$ are
[correctable](../knill-laflamme-conditions/is-correctable.md) by one recovery channel; by linearity so is every
combination of them. The code does not correct bit flips: $X_1$ and $I$ violate the Knill–Laflamme conditions, since
$X_1$ maps $|{+}{+}{+}\rangle$ to itself and $|{-}{-}{-}\rangle$ to $-|{-}{-}{-}\rangle$.

Proof: conjugation by $U = H^{\otimes 3}$ maps the projector of the bit-flip code to that of the phase-flip code and
$X_i$ to $Z_i$. If $R_r$ are the Kraus operators of the recovery for the
[bit-flip code](../bit-flip-and-shor-codes/is-correctable-bit-flip.md), then $U R_r U^{*}$ satisfy the definition of
correctability for the phase-flip code with the same scalars.

## Depends on

- [Three-qubit phase-flip code](three-qubit-phase-flip-code.md)
- [Correctable errors on a quantum code](../knill-laflamme-conditions/is-correctable.md)

## Proof depends on

- [The three-qubit bit-flip code corrects any single bit flip](../bit-flip-and-shor-codes/is-correctable-bit-flip.md)
- [Conjugation of Pauli operators by $H$, $S$ and CNOT](../clifford-group/conjugation-of-pauli-operators-by-h-s-and-cnot.md)
- [Correctable errors form a linear space](../knill-laflamme-conditions/is-correctable-of-forall-mem-span.md)
- [Necessity of the Knill–Laflamme conditions](../knill-laflamme-conditions/knill-laflamme-of-is-correctable.md)

## Sources

- D. G. Cory, M. D. Price, W. Maas, E. Knill, R. Laflamme, W. H. Zurek, T. F. Havel and S. S. Somaroo, *Experimental quantum error correction*, Phys. Rev. Lett. 81 (1998), 2152–2155, arXiv:quant-ph/9802018, the description of the three-bit phase code: $\alpha|000\rangle + \beta|100\rangle$ is encoded as $\alpha|{+}{+}{+}\rangle + \beta|{-}{-}{-}\rangle$, the convention used here, and each single phase error maps the encoded state to an orthogonal subspace, which is detected and undone.
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Exercise 7.1(b) and Section 7.15.1.
