# Crooks fluctuation theorem for work between equilibrium ensembles

Let a system with finite state space be driven by a protocol $\lambda_0 = \lambda_A, \lambda_1, \dots, \lambda_\tau = \lambda_B$ in discrete time, with Markov transition kernels $K_\lambda$ each satisfying detailed balance with respect to the canonical law $\pi_\lambda(x) \propto e^{-\beta E_\lambda(x)}$ (microscopic reversibility: the ratio of the probabilities of a path and of its time reverse under the reversed protocol is $e^{-\beta Q}$, with $Q$ the heat absorbed, Crooks 1999 Eq. (5)); states carry no odd variables (such as momenta), or these are reversed explicitly. The forward process starts in $\pi_{\lambda_A}$, and its step $t = 0, \dots, \tau - 1$ first changes the parameter from $\lambda_t$ to $\lambda_{t+1}$ at fixed state $x_t$ and then moves the state from $x_t$ to $x_{t+1}$ by $K_{\lambda_{t+1}}$. A path $x_0, \dots, x_\tau$ therefore has probability

$$\mathcal P_F(x_0, \dots, x_\tau) = \pi_{\lambda_A}(x_0)\prod_{t=0}^{\tau-1}K_{\lambda_{t+1}}(x_t, x_{t+1}),$$

work $W = \sum_{t=0}^{\tau-1}\bigl[E_{\lambda_{t+1}}(x_t) - E_{\lambda_t}(x_t)\bigr]$ and heat $Q = \sum_{t=0}^{\tau-1}\bigl[E_{\lambda_{t+1}}(x_{t+1}) - E_{\lambda_{t+1}}(x_t)\bigr]$, so that $E_{\lambda_B}(x_\tau) - E_{\lambda_A}(x_0) = W + Q$ (the first law, as in the source).

The reverse process runs the forward steps backwards in the opposite order. It starts at $x_\tau$ drawn from $\pi_{\lambda_B}$ with parameter $\lambda_\tau$, and its step undoing forward step $t$, for $t = \tau - 1, \dots, 0$, first moves the state from $x_{t+1}$ to $x_t$ by the same kernel $K_{\lambda_{t+1}}$ and then changes the parameter from $\lambda_{t+1}$ to $\lambda_t$ at fixed state $x_t$. The reversed path has probability

$$\mathcal P_R(x_\tau, \dots, x_0) = \pi_{\lambda_B}(x_\tau)\prod_{t=0}^{\tau-1}K_{\lambda_{t+1}}(x_{t+1}, x_t),$$

and reverse work $\sum_{t=0}^{\tau-1}\bigl[E_{\lambda_t}(x_t) - E_{\lambda_{t+1}}(x_t)\bigr] = -W$. Detailed balance gives $K_{\lambda_{t+1}}(x_t, x_{t+1})/K_{\lambda_{t+1}}(x_{t+1}, x_t) = e^{-\beta[E_{\lambda_{t+1}}(x_{t+1}) - E_{\lambda_{t+1}}(x_t)]}$ whenever either side is positive, so each forward factor is paired with a reverse factor of the same kernel and

$$\frac{\mathcal P_F(x_0, \dots, x_\tau)}{\mathcal P_R(x_\tau, \dots, x_0)} = \frac{\pi_{\lambda_A}(x_0)}{\pi_{\lambda_B}(x_\tau)}\,e^{-\beta Q} = e^{\beta(W + Q - \Delta F)}e^{-\beta Q} = e^{\beta(W - \Delta F)},$$

with $\Delta F = F_{\lambda_B} - F_{\lambda_A}$ and $F_\lambda = -\beta^{-1}\ln\sum_xe^{-\beta E_\lambda(x)}$. Let $P_F$ and $P_R$ be the laws of the work $W$ in the forward and reverse processes. Then

$$\frac{P_F(W)}{P_R(-W)} = e^{\beta (W - \Delta F)},$$

in the sense that $P_F$ and the reflected law of $-W$ under $P_R$ are mutually absolutely continuous with this Radon–Nikodym derivative (point probabilities when $W$ takes finitely many values; Crooks 1999, Sec. III, Eq. (11)). Integrating gives $E_F[e^{-\beta W}] = e^{-\beta\Delta F}$ (Crooks 1999, Eq. (3)).

## Depends on

- [Boltzmann probability of a state](../../../Chemistry/chemical-thermodynamics/canonical-ensemble-of-a-finite-system/boltzmann-prob.md)
- [Partition function of a finite system](../../../Chemistry/chemical-thermodynamics/canonical-ensemble-of-a-finite-system/partition-function.md)
- [Helmholtz free energy from the partition function](../../../Chemistry/chemical-thermodynamics/canonical-ensemble-of-a-finite-system/helmholtz-free-energy.md)
- [Detailed balance](../../../Probability/markov-chains/kolmogorov-s-criterion-for-reversibility/detailed-balance.md)

## Expansion

1. The model: driven Markov chains on a finite state space, the forward and reversed protocols, path probabilities, heat and work, and the detailed-balance (microscopic reversibility) hypothesis on each kernel $K_\lambda$.
2. The path-level identity above, with matching supports: by detailed balance with positive $\pi_\lambda$, $K_\lambda(x, y) > 0$ exactly when $K_\lambda(y, x) > 0$, so a path has positive forward probability exactly when its reversal has positive reverse probability.
3. Its pushforward to the law of $W$, stated as an equality of measures.
4. The Jarzynski equality as a corollary.
5. The general entropy-production version of the source, $\omega = \ln\rho_F(x_0) - \ln\rho_F(x_\tau) - \beta Q$, as a separate statement: it needs both endpoint conditions, the reverse process starting in the forward final law and the reverse final law equal to the forward initial law ($\omega_F = -\omega_R$); reverse-initial matching alone is not sufficient.

## Sources

- G. E. Crooks, Entropy production fluctuation theorem and the nonequilibrium work relation for free energy differences, Phys. Rev. E 60 (1999), 2721–2726, Eqs. (2), (3), (5) and Sec. III, Eq. (11). <https://arxiv.org/abs/cond-mat/9901352>
