# Statistical Difference and SZK

For constants $0\le\beta<\alpha^{2}\le1$, **Statistical Difference** $\mathrm{SD}^{\alpha,\beta}$ is the promise problem on pairs of Boolean circuits $(C_0,C_1)$ with the same input and output length: yes-instances have $\Delta(C_0(U),C_1(U))\ge\alpha$ and no-instances have $\Delta(C_0(U),C_1(U))\le\beta$, where $\Delta$ is total variation distance between output distributions on uniform inputs. $\mathrm{SZK}$ (promise version) is the class of promise problems polynomial-time reducible to $\mathrm{SD}^{2/3,1/3}$; by Sahai–Vadhan this coincides with statistical zero knowledge, and $\mathrm{SD}^{\alpha,\beta}$ is complete for it, so the class is the same, for all constants with $1>\alpha^{2}>\beta>0$. At the endpoints $\beta=0$ or $\alpha=1$, $\mathrm{SD}^{\alpha,\beta}$ still lies in $\mathrm{SZK}$, since its yes- and no-instances are yes- and no-instances of an interior pair $\mathrm{SD}^{\alpha',\beta'}$, but Sahai and Vadhan state completeness only for interior thresholds.

## Depends on

- [Promise problems and promise classes](../../randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/promise-and-randomized-classes/promise-problems.md)
- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](../../randomized-and-quantum-complexity/interactive-proofs/statistical-zero-knowledge-structure/promise-szk-and-hvszk.md)

## Proof depends on

- [Polarization lemma for statistical distance](../../../Probability/foundations/statistical-distance-and-couplings/polarization-lemma.md)

## Sources

- Amit Sahai and Salil Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM 50(2), 2003 (Theorem 3.1, Lemma 3.3 and the discussion after it, and Section 5 for $\mathrm{SD}^{\alpha,\beta}$ with $1>\alpha^2>\beta>0$).
