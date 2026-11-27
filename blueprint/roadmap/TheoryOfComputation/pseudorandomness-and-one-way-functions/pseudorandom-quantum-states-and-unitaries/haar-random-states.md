# Haar-random states and t-copy indistinguishability

For $d=2^{n}$, the *Haar measure* $\mu_d$ is the unique unitarily invariant probability measure on pure states of $\mathbb{C}^{d}$. The $t$-copy moment operator satisfies

$$
\mathbb{E}_{|\psi\rangle\sim\mu_d}\bigl[|\psi\rangle\langle\psi|^{\otimes t}\bigr]=\binom{d+t-1}{t}^{-1}\Pi_{\mathrm{sym}}^{(t)},
$$

where $\Pi_{\mathrm{sym}}^{(t)}$ is the projector onto the symmetric subspace of $(\mathbb{C}^{d})^{\otimes t}$. An ensemble of states is a *(state) $t$-design* if its $t$-copy moment operator equals this one, and two ensembles are *$t$-copy $\epsilon$-indistinguishable* if the trace distance between their $t$-copy moment operators is at most $\epsilon$.

## Depends on

- [Trace distance: metric, operational form and contractivity](../../../QuantumInformation/quantum-states-distances-and-entropy/remaining-clauses-of-trace-distance-and-contractivity.md)

## Sources

- Zhengfeng Ji, Yi-Kai Liu, Fang Song, "Pseudorandom Quantum States", CRYPTO (2018), IACR ePrint 2018/544.
- Tony Metger, Alexander Poremba, Makrand Sinha, Henry Yuen, "Simple Constructions of Linear-Depth t-Designs and Pseudorandom Unitaries", FOCS (2024), arXiv:2404.12647.
