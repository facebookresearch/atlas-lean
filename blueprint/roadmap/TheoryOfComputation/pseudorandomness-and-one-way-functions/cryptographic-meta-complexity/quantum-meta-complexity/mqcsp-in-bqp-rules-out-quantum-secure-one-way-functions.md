# Chia–Chou–Zhang–Zhang: MQCSP in BQP rules out quantum-secure one-way functions

If the quantum circuit minimization problem MQCSP is in BQP, then quantum-secure one-way functions do not exist; with quantum-secure iO it would further give $\mathsf{NP}\subseteq\mathsf{coRQP}$.

A quantum-secure one-way function is a polynomial-time computable $f$ that no quantum polynomial-time algorithm inverts with non-negligible probability on $f(x)$ for uniform $x$.

1. If MQCSP $\in$ BQP, then there is no quantum-secure one-way function.
2. Suppose quantum-secure indistinguishability obfuscation for polynomial-size circuits exists. Then MQCSP $\in$ BQP implies $\mathsf{NP}\subseteq\mathsf{coRQP}$, where coRQP is the class of one-sided-error quantum polynomial-time algorithms that always accept yes instances.

The same conclusions hold with the unitary version UMCSP in place of MQCSP.

## Expansion

From a quantum-secure one-way function $f$ build a quantum-secure PRG $G_f$ (the HILL construction, whose black-box security proof carries over to quantum adversaries), then by a GGM-style construction a generator $\hat G:\{0,1\}^{n}\to\{0,1\}^{2^{m}}$ with $m=O(\log n)$ whose outputs, viewed as truth tables of $g_x:\{0,1\}^{m}\to\{0,1\}$, are computable in time $\tilde O(n^{b})$, hence have quantum circuit complexity $\tilde O(n^{b})$. A random function on $m=d\log n$ bits has quantum circuit complexity above $2^{m}/((c+1)m)=\tilde O(n^{d})$ with high probability, so for $d\gg b$ a BQP algorithm for MQCSP with $s=2^{m}/((c+1)m)$ distinguishes $\hat G$ from random with advantage $1/\mathrm{poly}(n)$ and therefore inverts $f$. For item 2, apply item 1 to $f_C(r)=\mathrm{iO}(C,r)$. Given a circuit $C$ of size $s$, obfuscate it and ask the inverter for $f_{\perp_s}$, where $\perp_s$ is a canonical unsatisfiable circuit of size $s$, to find $r'$ with $\mathrm{iO}(\perp_s,r')$ equal to the obfuscation; reject if it succeeds. A satisfiable $C$ is never equivalent to $\perp_s$, so it is always accepted, while for unsatisfiable $C$ the indistinguishability of iO makes the inverter succeed with noticeable probability.

## Depends on

- [The Minimum Quantum Circuit Size Problem MQCSP](minimum-quantum-circuit-size-problem.md)
- [State and unitary minimum circuit size problems SMCSP and UMCSP](state-and-unitary-minimum-circuit-size-problems.md)
- [Indistinguishability and virtual black-box obfuscation](../../../../ComputerScience/cryptography/program-obfuscation/indistinguishability-and-virtual-black-box.md)
- [BQP](../../../complexity-classes/time-and-space-complexity-classes/bqp.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [Negligible functions](../../../complexity-classes/time-and-space-complexity-classes/negligible.md)

## Proof depends on

None.

## Informally uses

- [Pseudorandom generators exist if and only if one-way functions exist](../../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/pseudorandom-generators-exist-if-and-only-if.md)

## Sources

- Nai-Hui Chia, Chi-Ning Chou, Jiayu Zhang and Ruizhe Zhang, "Quantum Meets the Minimum Circuit Size Problem", *13th Innovations in Theoretical Computer Science Conference (ITCS 2022)*, LIPIcs, 2022, https://doi.org/10.4230/LIPIcs.ITCS.2022.47; numbering from arXiv:2108.03171v3 (Definitions 4.2, 4.3 and 4.9, Lemmas 4.6 and 4.7, Theorems 4.8 and 4.10, Corollaries 5.25 and 5.26).
