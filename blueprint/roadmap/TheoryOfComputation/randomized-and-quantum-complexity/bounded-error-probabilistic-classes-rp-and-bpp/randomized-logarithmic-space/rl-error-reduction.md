# Error reduction for RL

For every $L\in\mathsf{RL}$ and every constant $k$, there is a probabilistic logspace machine accepting members with probability at least $1-2^{-k}$ and never accepting non-members; more generally, the class is unchanged if the acceptance threshold $1/2$ is replaced by any constant in $(0,1)$.

## Proof sketch

Run the one-sided machine $k$ times in sequence on fresh coins, reusing the same work space, and accept if any run accepts.

## Depends on

- [Randomized logarithmic space RL and BPL](rl-and-bpl.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 7.
