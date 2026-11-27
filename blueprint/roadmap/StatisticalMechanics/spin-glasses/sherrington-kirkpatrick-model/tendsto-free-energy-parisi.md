# The Parisi formula for the SK model

For $\beta > 0$ and every field $h \in \mathbb{R}$, the values of the [Parisi functional](parisi-functional.md)
$\mathcal{P}_k(m, q)$, for $\xi(x) = \beta^2 x^2/2$ and $(k, m, q)$ ranging over the
[admissible Parisi parameters](is-parisi-parameter.md), have a greatest lower bound
$\mathcal{P}(\xi, h)$, and the [free energy](free-energy.md) converges to it:

$$\lim_{N \to \infty} F_N = \mathcal{P}(\xi, h) = \inf_{k, m, q}\mathcal{P}_k(m, q)$$

(Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), Theorem 1.1, which covers every Gaussian Hamiltonian whose covariance satisfies its
(1.3) for a function $\xi$ with (1.5); the SK model is the case above). In particular the values of the
functional are bounded below.

## Informally uses

- [Guerra's replica-symmetry-breaking bound for the SK model](free-energy-le-parisi-functional-eventua.md):
  the upper bound, by Guerra's interpolation scheme, which Talagrand's proof takes as its
  backbone.
