# Variance bound for single-snapshot estimators

For a single snapshot $\hat\rho$ and any observable $O$, the estimator $\hat o = \mathrm{Tr}(O\hat\rho)$ is unbiased, $\mathbb{E}[\hat o] = \mathrm{Tr}(O\rho)$, and

$$
\mathrm{Var}[\hat o] \le \left\| O - \tfrac{\mathrm{Tr}(O)}{2^n} I \right\|_{\mathrm{shadow}}^2 .
$$

Moreover $\|O_0\|^2_{\mathrm{shadow}} \le 3\,\mathrm{Tr}(O_0^2)$ for Clifford shadows, and $\|O\|^2_{\mathrm{shadow}} \le 4^{k} \|O\|_\infty^2$ for Pauli shadows when $O$ acts nontrivially on at most $k$ qubits.

## Proof sketch

Unbiasedness follows from $\mathbb{E}\hat\rho = \rho$; shifting $O$ by a multiple of the identity changes $\hat o$ by a constant, and the variance is at most the second moment, which by self-adjointness of $\mathcal{M}^{-1}$ is the quantity in the definition evaluated at $\sigma = \rho$. For Clifford shadows a $3$-design computation evaluates the second moment explicitly; for Pauli shadows the tensor product structure and the qubit computation give a factor $3$ per nontrivial Pauli, bounded by $4^k$ after expanding $O$ in the Pauli basis.

## Depends on

- [The shadow norm of an observable](shadow-norm-of-an-observable.md)
- [Classical shadows from randomized measurements](randomized-measurement-classical-shadow.md)

## Proof depends on

- [Inverse measurement channels for Clifford and Pauli shadows](inverse-measurement-channels-for-clifford-and-pauli-shadows.md)

## Sources

- Hsin-Yuan Huang, Richard Kueng, John Preskill, "Predicting many properties of a quantum system from very few measurements", Nature Physics 16 (2020); arXiv:2002.08953.
