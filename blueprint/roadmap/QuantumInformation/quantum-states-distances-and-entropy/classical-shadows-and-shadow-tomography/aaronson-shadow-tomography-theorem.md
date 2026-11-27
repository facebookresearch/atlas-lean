# Aaronson: shadow tomography with polylogarithmically many copies

Shadow tomography of $M$ two-outcome observables on a $D$-dimensional state is possible with

$$
N = \tilde O\!\left( \frac{\log^4 M \cdot \log D}{\varepsilon^4} \right)
$$

copies (for constant $\delta$), exponentially fewer than the $\Theta(D^2/\varepsilon^2)$ copies needed for full tomography when $M = 2^{O(\log D)}$.

## Proof sketch

Run an online learning algorithm (matrix multiplicative weights over density matrices, with mistake bound $O(\log D/\varepsilon^2)$) maintaining a hypothesis $\sigma$. In each round, use a quantum OR-type search on fresh copies to find an observable whose value on $\rho$ differs from its value on $\sigma$ by at least $\varepsilon$; gentle measurement makes the search reuse copies cheaply. Each found observable is a mistake for the online learner, so after $O(\log D/\varepsilon^2)$ rounds the hypothesis is accurate on all $M$ observables.

## Depends on

- [The shadow tomography problem](shadow-tomography-problem.md)

## Proof depends on

- [Gentle measurement lemma](gentle-measurement-lemma-for-shadow-tomography.md)
- [Regret bound for the matrix multiplicative weights update](../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/quantum-interactive-proofs-in-polynomial-space/matrix-multiplicative-weights-regret-bound.md)

## Sources

- Scott Aaronson, "Shadow tomography of quantum states", STOC (2018), SIAM Journal on Computing 49(5) (2020); arXiv:1711.01053.
