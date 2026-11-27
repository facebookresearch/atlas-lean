# The shadow norm of an observable

For an ensemble $\mathcal{U}$ with invertible measurement channel and an observable $O$, the *shadow norm* is

$$
\|O\|_{\mathrm{shadow}} = \max_{\sigma \text{ state}} \left( \mathbb{E}_{U \sim \mathcal{U}} \sum_{b} \langle b | U \sigma U^\dagger | b\rangle \, \langle b | U \mathcal{M}^{-1}(O) U^\dagger | b \rangle^2 \right)^{1/2} .
$$

It is a norm on traceless observables.

## Depends on

- [Classical shadows from randomized measurements](randomized-measurement-classical-shadow.md)

## Sources

- Hsin-Yuan Huang, Richard Kueng, John Preskill, "Predicting many properties of a quantum system from very few measurements", Nature Physics 16 (2020); arXiv:2002.08953.
