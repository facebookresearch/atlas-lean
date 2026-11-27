# EFI pairs are equivalent to quantum commitments, oblivious transfer and secure computation

The following are equivalent, by relativizing reductions (which may use the next-message functions of the protocols, not only oracle access to the ideal functionality): (i) EFI pairs exist; (ii) quantum bit commitments exist (in canonical form, computationally hiding and statistically binding, or the dual flavor); (iii) quantum oblivious transfer (computationally secure against malicious parties, possibly with quantum communication) exists; (iv) general secure multiparty computation for classical functionalities exists in the quantum world.

Zero knowledge is related one way at a time. If EFI pairs exist, then $\mathsf{QCZK}=\mathsf{QIP}$ (Theorem 6.4). Conversely, if some language with an honest-verifier $\mathsf{QCZK}$ proof is hard on average for $\mathsf{BQP}$ over a $\mathsf{BQP}$-samplable distribution, then EFI pairs secure against uniform $\mathsf{BQP}$ adversaries (not against the quantum-advice adversaries of the default definition) exist (Theorem 6.5); the worst-case assumption $\mathsf{BQP}\neq\mathsf{QCZK}$ yields only auxiliary-input EFI pairs (Theorem 6.8). In particular EFI is a minimal assumption for a large class of quantum cryptography.

## Proof sketch

Commitments to EFI: the two committed states form an EFI pair (statistical binding gives statistical farness, hiding gives indistinguishability). EFI to commitments: Yan's construction uses the purifications of $\rho_0,\rho_1$ and the duality lemma. Commitments imply OT and MPC by quantum protocols in the style of BB84-based OT with commitment-based checks (BCKM, GLSV), and minimal versions of OT or MPC yield EFI by considering the distributions of the receiver's view. Zero knowledge for $\mathsf{QIP}$ is a special case of secure two-party computation; the converse direction adapts the Ong–Vadhan route from honest-verifier zero knowledge to commitments, with Watrous's quantum techniques.

## Depends on

- [EFI pairs: efficient, statistically far, computationally indistinguishable states](efi-pairs.md)
- [Security with abort against malicious adversaries](../../../ComputerScience/cryptography/signatures-and-protocols/secure-multiparty-computation/security-with-abort-against-malicious.md)
- [Quantum interactive proofs (QIP) and IP subset QIP](../../randomized-and-quantum-complexity/quantum-interactive-proofs-and-ip-subset-qip.md)
- [Quantum bit commitments in canonical form](quantum-bit-commitments.md)

## Proof depends on

- [Hiding–binding duality for canonical quantum commitments](commitment-flavor-switching.md)
- [Oblivious transfer and secure computation from quantum commitments](quantum-ot-from-commitments.md)

## Sources

- Zvika Brakerski, Ran Canetti, Luowen Qian, "On the Computational Hardness Needed for Quantum Cryptography", ITCS (2023), arXiv:2209.04101 (Theorems 6.4, 6.5, 6.8).
- Jun Yan, "General Properties of Quantum Bit Commitments", ASIACRYPT (2022), IACR ePrint 2020/1488.
