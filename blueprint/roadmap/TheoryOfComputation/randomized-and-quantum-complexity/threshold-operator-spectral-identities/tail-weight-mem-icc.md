# Upper-tail weights are probabilities

For real numbers $\mu_0, \dots, \mu_{k-1}$ and $T$, the upper-tail weight is
$\tau(\mu, T) = \sum_b \prod_{i < k} (\mu_i \text{ if } b_i \text{ else } 1 - \mu_i)$, summed over
the Boolean strings $b$ of length $k$ with at least $T$ true entries. If every $\mu_i$ lies in
$[0, 1]$, then $\tau(\mu, T) \in [0, 1]$ for every threshold $T$.
