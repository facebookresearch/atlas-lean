# Sequential success counts versus the binomial effect

Under the hypotheses of the averaged disturbance bound (questions uniform and independent on $Q$, projective $M^x$ with commuting projective copies $R^y$, average pair defect at most $\chi$ and average copy defect at most $\zeta$), fix a success predicate on outcomes and let $\bar S = \mathbb{E}_x\sum_{a\ \text{successful}}R^x_a$ be the averaged success effect of the copies. For $k$ trials and threshold $t$,

$$
\Big|\ \mathbb{E}_{x\in Q^k}\sum_{g:\ \#\mathrm{succ}(g)\ge t}\operatorname{Re}\varphi\big(E^{(x)}_g\big)-\operatorname{Re}\varphi\big(B_{\ge t}(\bar S)\big)\Big|\le(1+\sqrt2)\Big(k\sqrt\zeta+k^2\sqrt{2\chi+8\zeta}\Big),
$$

where $E^{(x)}$ is the sequential measurement of $M^{x_1},\dots,M^{x_k}$ and $B_{\ge t}(\bar S) = \sum_{j\ge t}\binom kj\bar S^j(1-\bar S)^{k-j}$. The constants do not depend on the outcome alphabet or the dimension.

## Proof sketch

Interpolate by hybrids with $l$ trials already replaced by the binomial operator of the copies and $k-l$ still measured sequentially. Moving one trial from the sequential part to the binomial part transfers its first measurement to the commuting copy, at the cost of the average copy discrepancy and the transcript commutator error from the disturbance bound. Summing the $k$ steps gives the linear and quadratic terms.

## Depends on

- [Sequential projective measurements and their commutator defects](sequential-projective-measurements.md)
- [Operator Chernoff bound for binomial tails of an effect](binomial-tail-effects.md)

## Proof depends on

- [State-dependent disturbance of a sequential measurement](sequential-measurement-disturbance.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum soundness of the classical low individual degree test", arXiv:2009.12982, 2020.
