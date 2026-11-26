# Jarzynski nonequilibrium work equality for isolated Hamiltonian dynamics

Let $\Gamma$ be a phase space with Liouville measure $dz$ and $H_\lambda : \Gamma \to \mathbb{R}$, $\lambda \in [0, 1]$, a family of Hamiltonians; fix $\beta > 0$ and assume the partition functions $Z_\lambda = \int_\Gamma e^{-\beta H_\lambda(z)}\, dz$ are finite and positive for $\lambda = 0, 1$, with free energies $F_\lambda = -\beta^{-1}\ln Z_\lambda$. Let a protocol $\lambda(t)$ switch from $0$ to $1$ over $[0, t_s]$, and suppose the flow $\phi$ of the time-dependent Hamiltonian $H_{\lambda(t)}$ from time $0$ to $t_s$ is defined for every initial point, invertible and volume-preserving (Liouville). Draw $z_0$ from the canonical law $Z_0^{-1} e^{-\beta H_0}\, dz$ and let $W = H_1(\phi(z_0)) - H_0(z_0)$, the work done along the trajectory. Then

$$E\bigl[e^{-\beta W}\bigr] = \frac{Z_1}{Z_0} = e^{-\beta (F_1 - F_0)},$$

independently of the protocol (Jarzynski 1997, Eq. (2a)), by the change of variables $z = \phi(z_0)$.

## Proof depends on

- [Jensen's inequality](../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

1. The model: the phase space, the Hamiltonian family, the canonical law at $\lambda = 0$, the finiteness and positivity of $Z_0$ and $Z_1$, and the time-dependent Hamiltonian flow with its global existence, invertibility and volume preservation as hypotheses.
2. The work along a trajectory, $W = \int_0^{t_s} \dot\lambda\, \partial_\lambda H_\lambda(z(t))\, dt = H_1(\phi(z_0)) - H_0(z_0)$.
3. The equality by the change of variables $z = \phi(z_0)$ in $\int e^{-\beta H_1(\phi(z_0))}\, dz_0$.
4. Corollaries: if $W$ is integrable, $E[W] \ge F_1 - F_0$ by [Jensen's inequality](../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md); for instantaneous switching $W = H_1(z_0) - H_0(z_0)$ and the equality is the free-energy perturbation identity (Eq. (5) of the source).

Context outside this node: for a system coupled to a heat reservoir the same argument gives the equality for the total Hamiltonian, and its identification with the free energy of the system alone requires neglecting the interaction term (the source's weak-coupling step); the slow-switching limit (thermodynamic integration) needs quasistatic equilibration with a reservoir and does not hold for an isolated system in general. The Markovian version is a consequence of the [Crooks fluctuation theorem](crooks-fluctuation-theorem.md).

## Sources

- C. Jarzynski, Nonequilibrium equality for free energy differences, Phys. Rev. Lett. 78 (1997), 2690–2693, Eqs. (1), (2a), (5). <https://arxiv.org/abs/cond-mat/9610209>
