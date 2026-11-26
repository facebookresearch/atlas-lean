# Absorption rewards of strictly upper-triangular substochastic matrices

Let $V$ be a finite linearly ordered set and $S\in[0,1]^{V\times V}$ a nonnegative **strictly upper-triangular substochastic** matrix ($S_{uv}=0$ unless $u< v$, and $\sum_v S_{uv}\le 1$). Then $1-S$ is invertible with $(1-S)^{-1}=\sum_{k<|V|}S^{k}$, and for a target vertex $t$ the **reward vector** $p=(1-S)^{-1}e_t$ satisfies $0\le p\le 1$; $p_x$ is the probability that the Markov chain with transitions $S$ (killed with the missing mass) started at $x$ visits $t$. The acceptance probability of a time-layered probabilistic logspace computation is such an entry, with $V$ the time-stamped configurations.

## Depends on

- [Randomized logarithmic space RL and BPL](../rl-and-bpl.md)

## Sources

- OpenAI, "Exact Derandomization of Logarithmic Space: L = RL = BPL", Preprint, 2026.
