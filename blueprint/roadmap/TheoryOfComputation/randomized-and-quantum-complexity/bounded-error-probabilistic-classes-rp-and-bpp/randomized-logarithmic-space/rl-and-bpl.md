# Randomized logarithmic space RL and BPL

A probabilistic logspace machine is a deterministic machine with a read-only input tape, $O(\log n)$ work space and a read-once stream of fair coin flips, all of whose runs halt within a polynomial number of steps. $\mathsf{RL}$ is the class of languages $L$ with such a machine accepting every $x\in L$ with probability at least $1/2$ and every $x\notin L$ with probability $0$; $\mathsf{BPL}$ requires acceptance probability at least $2/3$ on members and at most $1/3$ on non-members. One has $\mathsf{L}\subseteq\mathsf{RL}\subseteq\mathsf{NL}$ and $\mathsf{RL}\subseteq\mathsf{BPL}$.

## Depends on

- [Deterministic logarithmic space](../../../complexity-classes/time-and-space-complexity-classes/log-space.md)
- [The complexity class NL](../../../complexity-classes/time-and-space-complexity-classes/nl.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 7.
- Noam Nisan, "Pseudorandom Generators for Space-Bounded Computation", Combinatorica 12(4), 449–461, 1992.
