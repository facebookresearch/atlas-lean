# Fault-tolerant preparation of encoded ancilla states for the seven-qubit code

For Steane's $[[7, 1, 3]]$ code there are [fault-tolerant preparation gadgets](../fault-tolerance-and-threshold/fault-tolerant-preparation-gadget.md)
for the encoded states $|\bar 0\rangle$ and $|\bar +\rangle$ and for the encoded magic state
$|\bar 0\rangle + e^{i\pi/4} |\bar 1\rangle$. The encoded $|\bar 0\rangle$ and $|\bar +\rangle$ come from a non-fault-tolerant
encoding circuit followed by verification against independently prepared ancillas, discarding the state when the
syndromes disagree, or by Shor-style measurement of the extra stabilizer $\bar Z$ or $\bar X$. The magic state is the
unique codeword in the $+1$ eigenspace of the Clifford operator $e^{i\pi/4} \bar X \bar S^{*}$, which can be measured
fault-tolerantly with verified cat states and repetition.

## Expansion

A sound expansion states and checks the constructions. Gottesman's survey describes them in prose and defers the details;
the verified preparation circuits and the measurement of $e^{i\pi/4} X P^{\dagger}$ with their fault counts are in
Aliferis, Gottesman and Preskill (2006) and in the references the survey gives ([10], [44] there). Each needs a page with
the circuit and the proof of properties Prep A and Prep B for $t = 1$.

## Depends on

- [Fault-tolerant preparation gadget](../fault-tolerance-and-threshold/fault-tolerant-preparation-gadget.md)
- [Steane's seven-qubit code](../small-stabilizer-codes/steane-seven-qubit-code.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.6.
- P. Aliferis, D. Gottesman and J. Preskill, *Quantum accuracy threshold for concatenated distance-3 codes*, Quantum Inf. Comput. 6 (2006), 97–165, arXiv:quant-ph/0504218.
