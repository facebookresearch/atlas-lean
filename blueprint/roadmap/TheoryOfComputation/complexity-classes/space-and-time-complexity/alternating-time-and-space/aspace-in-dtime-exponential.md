# Alternating space s is contained in deterministic time 2^{O(s)}

Let $s(n)\ge\log_2 n$. Every language accepted by an alternating multi-tape machine using work space $s(n)$ in every reachable configuration is in $\mathsf{DTIME}(2^{O(s(n))})$; without the assumption $s\ge\log n$, it is in $\mathsf{DTIME}(2^{O(\log n+s(n))})$. No constructibility hypothesis on $s$ is needed, and the alternating machine's branches need not halt.

## Proof sketch

The reachable configurations number $2^{O(\log n+s(n))}$. Starting from the halting accepting configurations, repeatedly mark existential configurations with a marked successor and universal ones with all successors marked; the least fixed point is reached after at most as many rounds as there are configurations, each round polynomial in that number.

## Depends on

- [Alternating time and space classes ATIME, ASPACE, AP, APSPACE and AL](alternating-time-and-space-classes.md)
- [Deterministic time classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dtime.md)

## Proof depends on

- [Configuration graph of a space-bounded machine](../configuration-graph-of-a-space-bounded-machine.md)
- [Exponential time bound from a space bound and halting](../../containments-between-time-and-space-classes/runs-in-time-exponential-of-space.md)

## Sources

- Ashok K. Chandra, Dexter C. Kozen and Larry J. Stockmeyer, "Alternation", Journal of the ACM 28(1), 1981.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
