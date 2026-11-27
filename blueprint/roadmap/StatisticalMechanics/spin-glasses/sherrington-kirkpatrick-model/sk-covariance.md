# Covariance function of the SK model

For $\beta \in \mathbb{R}$, the covariance function of the Sherrington–Kirkpatrick model is
$\xi(x) = \beta^2 x^2/2$. For $N \ge 1$, the SK [Hamiltonian](hamiltonian.md) satisfies
$\mathbb{E}H_N(\sigma^1)H_N(\sigma^2) = \frac{\beta^2}{N}\sum_{i<j}\sigma^1_i\sigma^1_j\sigma^2_i\sigma^2_j
= N\xi(R_{1,2}) - \beta^2/2$, where $R_{1,2} = \frac1N\sum_i\sigma^1_i\sigma^2_i$ is the overlap, so
condition (1.3) of Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006) holds with $c(N) = \beta^2/(2N)$. For $\beta > 0$, $\xi$ is even,
smooth, vanishes at $0$, and $\xi'$ and $\xi''$ are positive on $(0, \infty)$.
