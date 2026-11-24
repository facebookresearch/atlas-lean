# Integral fluctuation theorem for total entropy production

Consider a master equation on a finite state space with time-dependent rates $r_{\lambda(\tau)}(n, m)$, $0 \le \tau \le t$, such that $r_\lambda(m, n) > 0$ whenever $r_\lambda(n, m) > 0$, and let $p(n, \tau)$ be its solution from the initial law $p_0$. Along a trajectory $n(\tau)$ let $\Delta s = -\ln p(n(t), t) + \ln p_0(n(0))$ be the change of system entropy and $\Delta s_m = \sum_{\text{jumps } n \to m} \ln\frac{r(n, m)}{r(m, n)}$ the medium entropy (equal to the heat dissipated divided by $T$, in units $k_B = 1$, under local detailed balance), and $\Delta s_{\mathrm{tot}} = \Delta s + \Delta s_m$. If the path law of the process reversed in time, with reversed protocol and started from $p(\cdot, t)$, is absolutely continuous with respect to the forward path law (for example, if $p_0$ charges every state), then
$$E\bigl[e^{-\Delta s_{\mathrm{tot}}}\bigr] = 1$$
for every driving over a finite time interval (Seifert 2005). Without the support condition the expectation is the mass of the absolutely continuous part and can be smaller: for two states with rate $1$ in each direction, $p_0 = (1, 0)$ and $t = (\ln 2)/2$, one gets $p(\cdot, t) = (3/4, 1/4)$, $\Delta s_m = 0$ and $E[e^{-\Delta s_{\mathrm{tot}}}] = 5/8$.

## Expansion

1. The model: driven master equations with reversible transition graphs, path probabilities, and the system and medium entropies; the identification of $\Delta s_m$ with heat over temperature under local detailed balance.
2. The identity $E_P[\exp(-\ln \frac{dP}{d\tilde P})] = \tilde P(\text{absolutely continuous part})$ for path laws, and the path-probability ratio $dP/d\tilde P = e^{\Delta s_{\mathrm{tot}}}$ with the reversed process started from $p(\cdot, t)$.
3. The support condition, and the two-state counterexample showing it cannot be dropped.
4. The overdamped Langevin case of the source, with the Einstein relation between mobility and noise, the Stratonovich convention for the heat, and the regularity of $p$ as hypotheses.
5. Corollaries: $E[\Delta s_{\mathrm{tot}}] \ge 0$ by [Jensen's inequality](../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md); and, replacing the actual final law $p(\cdot, t)$ by the equilibrium law of the final Hamiltonian (a different functional, as the source notes), the [Jarzynski equality](../../../StatisticalMechanics/nonequilibrium-fluctuation-relations/jarzynski-and-crooks-relations/jarzynski-nonequilibrium-work-equality.md).

## Sources

- U. Seifert, Entropy production along a stochastic trajectory and an integral fluctuation theorem, Phys. Rev. Lett. 95 (2005), 040602. <https://arxiv.org/abs/cond-mat/0503686>
