# Statistical Difference and SZK

For constants $0\le\beta<\alpha^{2}\le1$, **Statistical Difference** $\mathrm{SD}^{\alpha,\beta}$ is the promise problem on pairs of Boolean circuits $(C_0,C_1)$ with the same input and output length: yes-instances have $\Delta(C_0(U),C_1(U))\ge\alpha$ and no-instances have $\Delta(C_0(U),C_1(U))\le\beta$, where $\Delta$ is total variation distance between output distributions on uniform inputs. $\mathrm{SZK}$ (promise version) is the class of promise problems polynomial-time reducible to $\mathrm{SD}^{2/3,1/3}$; by Sahai–Vadhan this coincides with statistical zero knowledge, and the class is the same for all constant thresholds with $\beta<\alpha^{2}$.

## Depends on

- [Promise problems and promise classes](../../randomized-and-quantum-complexity/promise-and-randomized-classes/promise-problems.md)

## Sources

- Amit Sahai and Salil Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM 50(2), 2003.
