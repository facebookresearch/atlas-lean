# Sherrington–Kirkpatrick model

The Sherrington–Kirkpatrick (SK) model has configurations $\sigma \in \{-1, 1\}^N$, the random
Hamiltonian $H_N(\sigma) = -\frac{\beta}{\sqrt N}\sum_{i<j} g_{ij}\sigma_i\sigma_j$ with independent
standard Gaussian couplings $g_{ij}$, and the free energy
$F_N = \frac1N \mathbb{E}\log\sum_\sigma \exp\big(H_N(\sigma) + h\sum_i \sigma_i\big)$. Its
covariance is a function of the overlap $R_{1,2} = \frac1N\sum_i \sigma^1_i\sigma^2_i$:
$\mathbb{E} H_N(\sigma^1) H_N(\sigma^2) = N\xi(R_{1,2}) - \beta^2/2$ with $\xi(x) = \beta^2 x^2/2$.

The Parisi formula identifies $\lim_N F_N$ as the infimum of the Parisi functional
$\mathcal{P}_k(m, q)$ over admissible parameters
$0 = m_0 \le \dots \le m_k = 1$ and $0 = q_0 \le \dots \le q_{k+1} = 1$. Guerra's interpolation
gives the upper bound; Talagrand proved the matching lower bound by controlling two coupled
copies of the system.

Source: M. Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), 221–263, Section 1.

- [Ising spin of a Boolean](spin.md)
- [Sherrington–Kirkpatrick Hamiltonian](hamiltonian.md)
- [Law of the couplings](coupling-law.md)
- [Free energy of the SK model](free-energy.md)
- [Covariance function of the SK model](sk-covariance.md)
- [Admissible Parisi parameters](is-parisi-parameter.md)
- [Replica-symmetric parameters are admissible](is-parisi-parameter-replica-symmetric.md)
- [One step of the Parisi recursion](parisi-step.md)
- [The Parisi recursion](parisi-recursion.md)
- [The Parisi functional](parisi-functional.md)
- [Guerra's replica-symmetry-breaking bound for the SK model at every system size](free-energy-le-parisi-functional.md)
- [Guerra's replica-symmetry-breaking bound for the SK model](free-energy-le-parisi-functional-eventua.md)
- [The Parisi formula for the SK model](tendsto-free-energy-parisi.md)
- [Gaussian SK energy and the single-site heat bath](gaussian-sk-heat-bath.md)

## Related topics

- [Ising model on a finite graph](../../spin-models/ising-model-on-a-finite-graph/README.md): the
  ferromagnetic model with deterministic couplings on a graph, against which the SK model's
  random couplings on the complete graph are set.
- [Generic chaining and Gaussian processes](../../../Probability/high-dimensional-probability/generic-chaining-and-gaussian-processes/README.md):
  $(H_N(\sigma))_\sigma$ is a Gaussian process indexed by $\{-1, 1\}^N$, whose supremum is the
  ground-state energy; Talagrand studies both in the same Gaussian framework.

- [Critical SK covariance norm and linear inverse-Rayleigh scale](critical-covariance-and-linear-rayleigh.md)
- [Critical SK polynomial lower and subexponential upper mixing bounds](critical-mixing-subexponential-upper-bound.md)
- [Critical SK obstruction for realized equilibrium starting states](critical-realized-equilibrium-starts.md)
- [Critical SK worst-start mixing lower bounds](critical-worst-start-mixing-lower-bounds.md)
- [Discrete SK ratio cutoff below inverse temperature one half](discrete-high-temperature-ratio-cutoff.md)
- [High-temperature SK heat-bath Poincaré and gap bounds](high-temperature-poincare-gap.md)
- [Low-temperature SK obstructions from Gibbs-distributed starts](low-temperature-realized-start-barriers.md)
- [Full support and diffusion identities for zero-temperature SK minimizers](zero-temperature-full-support.md)
- [Zero-temperature SK value identities and finite Gaussian approximants](zero-temperature-value-and-gaussian-approximation.md)
