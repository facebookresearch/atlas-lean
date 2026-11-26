# The upper-tail weight is a Poisson-binomial tail

For real numbers $\mu_0, \dots, \mu_{k-1}$ and a threshold $T \in \mathbb{R}$, the upper-tail weight $\sum_b \prod_i (\mu_i \text{ if } b_i \text{ else } 1 - \mu_i)$, the sum over strings $b$ of $k$ Booleans whose number of true entries is at least $T$, equals the Poisson-binomial tail of $(\mu_i)$ at $\lceil T \rceil$, where the ceiling is taken in the natural numbers (so it is $0$ for $T \le 0$).
