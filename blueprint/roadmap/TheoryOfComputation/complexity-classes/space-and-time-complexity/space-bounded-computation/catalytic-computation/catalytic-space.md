# Catalytic space computation

A **catalytic** Turing machine with work space $s(n)$ and catalytic space $c(n)$ has, besides a read-only input and $s(n)$ ordinary work cells (initially blank), a tape of $c(n)$ cells whose initial content $\tau\in\{0,1\}^{c(n)}$ is arbitrary. The machine computes $f$ catalytically if for **every** input $x$ and **every** initial catalytic content $\tau$ it halts with output $f(x)$ and with the catalytic tape restored exactly to $\tau$. $\mathsf{CL}$ is the class of languages decided with $s=O(\log n)$ and $c=n^{O(1)}$.

## Depends on

- [Deterministic logarithmic space](../../../time-and-space-complexity-classes/log-space.md)

## Sources

- Harry Buhrman et al., "Computing with a Full Memory: Catalytic Space", Proceedings of the 46th Annual ACM Symposium on Theory of Computing, 2014.
