# Read-once branching program and space-bounded pseudorandom generator

A *read-once branching program* of width $w$ and length $\ell$ is a layered directed graph with layers $V_0, \dots, V_\ell$, each of size at most $w$, a start vertex in $V_0$, a set of accepting vertices in $V_\ell$, and for each vertex of $V_{i-1}$ two outgoing edges into $V_i$ labelled $0$ and $1$; on input $y \in \{0,1\}^\ell$ it follows the edge labelled $y_i$ at step $i$. Width $2^s$ corresponds to space $s$. A generator $G : \{0,1\}^d \to \{0,1\}^\ell$ is an *$(s, \varepsilon)$-pseudorandom generator* if for every read-once program $P$ of width $2^s$ and length $\ell$,

$$\bigl|\Pr[P(G(U_d)) = 1] - \Pr[P(U_\ell) = 1]\bigr| \le \varepsilon.$$

## Depends on

- [Distinguishing advantage](../../../ComputerScience/cryptography/security-games/games-and-advantages/advantage.md)

## Sources

- N. Nisan, "Pseudorandom Generators for Space-Bounded Computation", Combinatorica 12(4), 1992.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012.
