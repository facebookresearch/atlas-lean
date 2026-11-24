# Crooks fluctuation theorem for work between equilibrium ensembles

Let a system with finite state space be driven by a protocol $\lambda_0 = \lambda_A, \lambda_1, \dots, \lambda_\tau = \lambda_B$ in discrete time, with Markov transition kernels $K_\lambda$ each satisfying detailed balance with respect to the canonical law $\pi_\lambda(x) \propto e^{-\beta E_\lambda(x)}$ (microscopic reversibility: the ratio of the probabilities of a path and of its time reverse under the reversed protocol is $e^{-\beta Q}$, with $Q$ the heat absorbed, Crooks 1999 Eq. (5)); states carry no odd variables (such as momenta), or these are reversed explicitly. Start the forward process in $\pi_{\lambda_A}$ and the reverse process, driven by the reversed protocol, in $\pi_{\lambda_B}$, and let $P_F$ and $P_R$ be the laws of the work $W$ in the two processes. Each step first changes the parameter from $\lambda_t$ to $\lambda_{t+1}$ at fixed state and then moves the state by $K_{\lambda_{t+1}}$; along a path $x_0, \dots, x_\tau$ the work is $W = \sum_{t=0}^{\tau-1}\bigl[E_{\lambda_{t+1}}(x_t) - E_{\lambda_t}(x_t)\bigr]$ and the heat is $Q = \sum_{t=0}^{\tau-1}\bigl[E_{\lambda_{t+1}}(x_{t+1}) - E_{\lambda_{t+1}}(x_t)\bigr]$, so that $E_{\lambda_B}(x_\tau) - E_{\lambda_A}(x_0) = W + Q$ (the first law, as in the source). Then, with $\Delta F = F_{\lambda_B} - F_{\lambda_A}$,

$$\frac{P_F(W)}{P_R(-W)} = e^{\beta (W - \Delta F)},$$

in the sense that $P_F$ and the reflected law of $-W$ under $P_R$ are mutually absolutely continuous with this Radon–Nikodym derivative (point probabilities when $W$ takes finitely many values). Integrating gives $E_F[e^{-\beta W}] = e^{-\beta\Delta F}$ (Crooks 1999, Eq. (3) and Sec. III).

## Expansion

1. The model: driven Markov chains on a finite state space, the forward and reversed protocols, path probabilities, heat and work, and the detailed-balance (microscopic reversibility) hypothesis on each kernel $K_\lambda$.
2. The path-level identity: the forward path law starting from $\pi_{\lambda_A}$ and the reversed path law starting from $\pi_{\lambda_B}$ have ratio $e^{\beta(W - \Delta F)}$ on each path, with matching supports.
3. Its pushforward to the law of $W$, stated as an equality of measures.
4. The Jarzynski equality as a corollary.
5. The general entropy-production version of the source, $\omega = \ln\rho_F(x_0) - \ln\rho_F(x_\tau) - \beta Q$, as a separate statement: it needs both endpoint conditions, the reverse process starting in the forward final law and the reverse final law equal to the forward initial law ($\omega_F = -\omega_R$); reverse-initial matching alone is not sufficient.

## Sources

- G. E. Crooks, Entropy production fluctuation theorem and the nonequilibrium work relation for free energy differences, Phys. Rev. E 60 (1999), 2721–2726, Eqs. (2), (3), (5) and Sec. III. <https://arxiv.org/abs/cond-mat/9901352>
