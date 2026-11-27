# Poisson-diluted Ising energy and conditional cavity weights

At size $N>0$ use a Poisson number of interactions of mean $\alpha N$ with independently sampled interactions and independent uniform lists of $p$ vertex labels, sampled with replacement. The random log weight of a spin configuration is the sum of the interaction values on the sampled spins and of the site fields times spins. Take the real log of the sum over configurations; the pressure is its expectation divided by $N$. For trial cavity messages use $Q_x(s)=e^{xs}/(2\cosh x)$, the edge weight $\sum_s e^{\theta(s)}\prod_iQ_{x_i}(s_i)$, and the corresponding single-spin message obtained by fixing the indicated coordinate and summing the other $p-1$. The sign moment, factorization and integrability assumptions belong to the variational theorem for this model, not to all Poisson-diluted spin systems.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DilutedSpin.lean#L12-L144)
