# EFI pairs: efficient, statistically far, computationally indistinguishable states

An *EFI pair* is a quantum polynomial-time algorithm $\mathsf{Gen}(1^\lambda,b)$ outputting a mixed state $\rho_b$ for $b\in\{0,1\}$ such that (i) $\rho_0$ and $\rho_1$ are statistically far: $\frac{1}{2}\|\rho_0-\rho_1\|_1\ge 1/\mathrm{poly}(\lambda)$ (equivalently, after amplification, $1-\mathrm{negl}(\lambda)$); and (ii) they are computationally indistinguishable: every quantum polynomial-time distinguisher has negligible advantage. EFI pairs are the quantum analogue of the classical EFID pairs, which are equivalent to one-way functions classically.

## Depends on

- [Trace distance: metric, operational form and contractivity](../../../QuantumInformation/quantum-states-distances-and-entropy/remaining-clauses-of-trace-distance-and-contractivity.md)
- [BQP](../../complexity-classes/time-and-space-complexity-classes/bqp.md)

## Sources

- Zvika Brakerski, Ran Canetti, Luowen Qian, "On the Computational Hardness Needed for Quantum Cryptography", ITCS (2023), arXiv:2209.04101.
