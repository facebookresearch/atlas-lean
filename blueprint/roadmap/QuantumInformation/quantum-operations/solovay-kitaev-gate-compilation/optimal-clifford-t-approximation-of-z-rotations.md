# Ross-Selinger: optimal Clifford+T approximation of z-rotations

There is a probabilistic polynomial-time algorithm (under a number-theoretic factoring assumption) that, given $\theta$ and $\varepsilon$, outputs an ancilla-free Clifford+T circuit approximating $R_z(\theta) = \mathrm{diag}(e^{-i\theta/2}, e^{i\theta/2})$ within $\varepsilon$ in operator norm with T-count $3\log_2(1/\varepsilon) + O(\log\log(1/\varepsilon))$ for generic $\theta$, which is optimal among all ancilla-free Clifford+T approximations.

## Proof sketch

Unitaries exactly representable over Clifford+T are the matrices over the ring $\mathbb{Z}[1/\sqrt2, i]$; their T-count equals the least denominator exponent. Approximation reduces to enumerating lattice points of $\mathbb{Z}[\omega]$ in a thin slice of the unit disk, found with a two-dimensional grid problem, and solving a norm equation in $\mathbb{Z}[\sqrt 2]$, which is efficient when the relevant integer can be factored.

## Proof depends on

- [Dense inverse-closed gate sets and epsilon-nets in SU(d)](dense-gate-sets-and-epsilon-nets.md)
- [Volume lower bound: logarithmic word length is necessary](volume-lower-bound-for-gate-approximation.md)

## Sources

- Neil J. Ross, Peter Selinger, "Optimal ancilla-free Clifford+T approximation of z-rotations", Quantum Information and Computation 16 (2016); arXiv:1403.2975.
