# The Minimum Quantum Circuit Size Problem MQCSP

MQCSP asks, given the truth table of a Boolean function $f$ and a size bound $s$, whether some quantum circuit with at most $s$ gates and $t$ ancillas computes $f(x)$ with probability at least $\alpha$ on every input, versus every such circuit erring badly on some input.

Fix a universal gate set $G$. Let $n,s,t\in\mathbb{N}$ with $t\le s$, let $f:\{0,1\}^{n}\to\{0,1\}$, and let $\alpha,\beta\in(1/2,1)$ with $\alpha-\beta\ge 1/\mathrm{poly}(2^{n})$. **MQCSP$_{\alpha,\beta}$** is the promise problem:

- Input: the truth table $tt(f)$, the size parameter $s$ in unary and the ancilla parameter $t$.
- Yes: some quantum circuit $C$ with at most $s$ gates on at most $n+t$ qubits satisfies, for all $x\in\{0,1\}^{n}$,

$$
\left\|(\langle f(x)|\otimes I_{n+t-1})\,C\,|x,0^{t}\rangle\right\|^{2}\ge\alpha .
$$

- No: for every quantum circuit $C$ with at most $s$ gates on at most $n+t$ qubits there is $x$ with that quantity at most $\beta$.

The thresholds exceed $1/2$ because measuring $|+\rangle$ already outputs $f(x)$ with probability $1/2$. The gap version MQCSP$_{a,b}[s,s',t]$ with $t\le s<s'\le 2^{O(n)}$ uses thresholds $2/3$ for circuits of size $s$ (yes) and $1/2$ for all circuits of size $s'$ (no). By Solovay–Kitaev, changing the universal gate set multiplies circuit size by a factor $\mathrm{polylog}(s/\epsilon)$ at a cost of $\epsilon^{2}/2$ in the success amplitude: a size-$s$ circuit achieving $\ge 1-\delta$ yields one over the other gate set achieving $\ge 1-\delta-\epsilon^{2}/2$. MQCSP is in NP when only linearly many ancillas are allowed, and MQCSP $\in$ QCMA in general.

## Expansion

Unlike classical MCSP, a quantum circuit may compute $f$ only with bounded error, which forces a promise gap, and the number of ancillas matters for verification: with linearly many ancillas a verifier can write down the $2^{O(n)}$-dimensional unitary, but with superlinearly many it cannot, and a quantum verifier instead tests the circuit on all $2^{n}$ inputs with repeated runs. Classical MCSP and MQCSP are incomparable because quantum circuits can be smaller for some functions.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Universal gate set](../../../../QuantumInformation/quantum-error-correction/universal-gate-sets/universal-gate-set.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The class QCMA of quantum verification with classical witnesses](../../../randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/witness-preserving-amplification-and-black-box-groups/quantum-classical-merlin-arthur.md)

## Proof depends on

None.

## Sources

- Nai-Hui Chia, Chi-Ning Chou, Jiayu Zhang and Ruizhe Zhang, "Quantum Meets the Minimum Circuit Size Problem", *13th Innovations in Theoretical Computer Science Conference (ITCS 2022)*, LIPIcs, 2022, https://doi.org/10.4230/LIPIcs.ITCS.2022.47; numbering from arXiv:2108.03171v3 (Definitions 2.5, 3.2 and 3.4, Claim 3.3, Theorems 3.8 and 3.9).
