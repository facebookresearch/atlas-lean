# Minimal depth of optimal fanout-k prefix circuits is log_{α_k} N ± O(1)

For $k\ge2$ let $\alpha_k$ be the unique positive root of $P_k(x)=x^k-x^{k-2}-\cdots-x-2$; then $1<\alpha_k<\varphi=(1+\sqrt5)/2$, $\alpha_k$ increases with $k$ and $\alpha_k\to\varphi$. The minimal depth $D_k(N)$ of a zero-deficiency universal prefix circuit with fanout at most $k$ on $N$ inputs satisfies $|D_k(N)-\log_{\alpha_k}N|\le C_k$ for a constant $C_k$ depending only on $k$.

## Proof sketch

The characteristic polynomial of the linear recurrence for $w_k^\ast(D)$ is $P_k$, so $w_k^\ast(D)=\Theta(\alpha_k^D)$; inverting gives the depth estimate.

## Depends on

- [Universal prefix circuits and fanout-bounded optimality](universal-prefix-circuits.md)

## Proof depends on

- [Width recurrences for optimal fanout-bounded prefix circuits](width-recurrence-for-optimal-prefix-circuits.md)

## Sources

- Igor S. Sergeev, "A Note on the Depth of Optimal Fanout-Bounded Prefix Circuits", 2025.
