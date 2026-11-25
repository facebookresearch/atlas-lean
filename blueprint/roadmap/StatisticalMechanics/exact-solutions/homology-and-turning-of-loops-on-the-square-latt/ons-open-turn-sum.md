# Open turning sum of a direction list

For a list $(d_0, \dots, d_{m-1})$ of directions in $\{0, 1, 2, 3\}$, the open turning sum is $\sum_{i=0}^{m-2} \tau(d_i, d_{i+1})$, which is $0$ when $m \le 1$; here $\tau(\mu, \nu)$ is the turn from direction $\mu$ to direction $\nu$: $0$ if $\nu = \mu$, $+1$ if $\nu = \mu + 1$, $0$ if $\nu = \mu + 2$ (a reversal) and $-1$ if $\nu = \mu + 3$, indices mod $4$.
