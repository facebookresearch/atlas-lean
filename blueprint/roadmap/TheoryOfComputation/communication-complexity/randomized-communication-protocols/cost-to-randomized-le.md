# Cost of the induced randomized protocol

Let $R$ be a nonempty finite set and $P = (p_r)_{r \in R}$ a public-coin protocol for inputs $X$ and $Y$
with random strings in $R$. The randomized protocol induced by $P$, which draws $r \in R$ uniformly and
runs $p_r$, has cost at most the cost of $P$: the largest depth of a protocol in its support is at
most $\max_{r \in R} \operatorname{depth}(p_r)$.
