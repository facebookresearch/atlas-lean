# Size bound for the grid row network

Let $g, L, m, B, b \in \mathbb{N}$ with $m \ge 1$, let the row set $\rho$ and the column set
$\gamma$ both have $g$ elements, and assume:

- $|\Lambda| \le 2^L$ and $|\Delta| \le 2^L$;
- $|R_w(h)| \le 2^B$ for every cell $w$ and every $h$;
- $G_\omega(x, y, u, v) = \sum_{\theta \in T_\omega} \mathrm{top}_\omega(x, y, \theta) \,
  \mathrm{bot}_\omega(u, v, \theta)$ for all $\omega, x, y, u, v$;
- $|T_\omega| \le 2^{\kappa_\omega}$ and $\kappa_\omega \le 2 m L$ for every $\omega$;
- $|\mathrm{top}_\omega(x, y, \theta)| \le 2^b$, $|\mathrm{bot}_\omega(u, v, \theta)| \le 2^b$ and
  $|G_\omega(x, y, u, v)| \le 2^b$ for all arguments.

Then the row network built from $\Lambda, \Delta, R, T, \mathrm{top}, \mathrm{bot}, \kappa, L$ has
size parameters $m g^3 L$ and $g B + g^2 b$.
