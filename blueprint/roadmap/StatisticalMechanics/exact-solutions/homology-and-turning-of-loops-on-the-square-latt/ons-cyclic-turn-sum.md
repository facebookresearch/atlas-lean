# Cyclic turning sum of a direction list

For a list $(d_0, \dots, d_{m-1})$ of directions in $\{0, 1, 2, 3\}$, the cyclic turning sum is

$$\sum_{i=0}^{m-2} \tau(d_i, d_{i+1}) + \tau(d_{m-1}, d_0)$$

for $m \ge 1$ (for $m = 1$ it is $\tau(d_0, d_0) = 0$), and $0$ for the empty list, where $\tau(\mu, \nu)$ is the turn from direction $\mu$ to direction $\nu$: $0$ if $\nu = \mu$, $+1$ if $\nu = \mu + 1$, $0$ if $\nu = \mu + 2$ (a reversal) and $-1$ if $\nu = \mu + 3$, indices mod $4$.
