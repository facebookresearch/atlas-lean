# State and unitary minimum circuit size problems SMCSP and UMCSP

UMCSP asks whether a given $2^{n}\times 2^{n}$ unitary is $\alpha$-approximated by a quantum circuit of $s$ gates; SMCSP asks the same for an $n$-qubit state, given only many copies of the state rather than a classical description.

Let $n,s,t\in\mathbb{N}$ with $t\le s$ and $\alpha,\beta\in(0,1]$.

**UMCSP$_{\alpha,\beta}$.** Input: a unitary $U\in\mathbb{C}^{2^{n}\times 2^{n}}$, $s$ in unary and an ancilla parameter $t$. Yes: some quantum circuit $C$ with at most $s$ gates on at most $n+t$ qubits satisfies, for all $|\psi\rangle\in\mathbb{C}^{2^{n}}$,

$$
\left\|(\langle\psi|\otimes I_t)(U^{\dagger}\otimes I_t)\,C\,|\psi,0^{t}\rangle\right\|^{2}\ge\alpha .
$$

No: for every such circuit some $|\psi\rangle$ gives a value at most $\beta$.

**SMCSP$_{\alpha,\beta}$.** Input: $s$ and $n$ in unary, the ancilla parameter $t$, and access to arbitrarily many copies of an $n$-qubit state $|\phi\rangle$. Yes: some circuit $C$ with at most $s$ gates on at most $n+t$ qubits has $\|(\langle\phi|\otimes I_t)C|0^{n+t}\rangle\|^{2}\ge\alpha$. No: every such circuit has this value at most $\beta$. (The source writes $I_{n+t-1}$, carried over from MQCSP, where the projected register is one qubit; since $\langle\phi|$ acts on $n$ qubits, the identity acts on the remaining $t$, and this page corrects it.) An algorithm for SMCSP is efficient if it runs in time $\mathrm{poly}(n,t,s)$, and so uses polynomially many copies.

Entries of $U$ are given to $s\cdot\ell_G$ bits of precision, where $\ell_G$ bounds the bit length of gate entries. UMCSP is in QCMA for $\beta\le 1-\mathrm{poly}(1/2^{n})$ and $\alpha>1-2^{-2n-20}(1-\beta)^{4}$, and SMCSP with gap $|\alpha-\beta|\ge 1/\mathrm{poly}(s)$ has a QCMA protocol (the source's Theorem 5.9 prints $|\alpha-\beta|\ge\mathrm{poly}(s)$, an evident misprint for $1/\mathrm{poly}(s)$).

## Expansion

These problems measure the circuit complexity of quantum objects rather than Boolean functions. The swap test lets a QCMA verifier compare a claimed circuit's output with copies of $|\phi\rangle$; for unitaries the verifier tests the circuit on basis states and their superpositions, which is why the thresholds for UMCSP are so close to $1$. Both admit search-to-decision reductions without ancillas, and MQCSP with gap reduces to UMCSP through the trivial unitary encoding of a Boolean function.

## Depends on

- [The Minimum Quantum Circuit Size Problem MQCSP](minimum-quantum-circuit-size-problem.md)
- [The class QCMA of quantum verification with classical witnesses](../../../randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/witness-preserving-amplification-and-black-box-groups/quantum-classical-merlin-arthur.md)

## Proof depends on

None.

## Sources

- Nai-Hui Chia, Chi-Ning Chou, Jiayu Zhang and Ruizhe Zhang, "Quantum Meets the Minimum Circuit Size Problem", *13th Innovations in Theoretical Computer Science Conference (ITCS 2022)*, LIPIcs, 2022, https://doi.org/10.4230/LIPIcs.ITCS.2022.47; numbering from arXiv:2108.03171v3 (Definitions 5.1 and 5.2, Remarks 7 and 8, Theorems 5.5, 5.9, 5.16, 5.18 and 5.23).
