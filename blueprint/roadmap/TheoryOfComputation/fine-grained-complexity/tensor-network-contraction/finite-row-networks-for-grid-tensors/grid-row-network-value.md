# Grid row network computes the grid value

Let $G_\omega$ be kernels with $G_\omega(x, y, u, v) = \sum_{\theta \in T_\omega}
\mathrm{top}_\omega(x, y, \theta) \, \mathrm{bot}_\omega(u, v, \theta)$ for all $\omega, x, y, u, v$.
Then the value of the row network built from $\Lambda, \Delta, R, T, \mathrm{top}, \mathrm{bot},
\kappa, L$ equals the grid value of $R$ with edge labels $\Lambda$, diagonal labels $\Delta$ and
kernels $G$.
