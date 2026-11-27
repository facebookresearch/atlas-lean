# Feasible clique-cover instances

A clique-cover instance $(n, E, \ell)$ is feasible when there is a map $c$ from the vertices $0, \dots, n-1$ to $\{0, \dots, \ell - 1\}$ such that any two distinct vertices with the same value are adjacent in the graph of the instance. Each class of $c$ is then a clique, so the vertex set is the union of $\ell$ or fewer cliques, which is Karp's condition; conversely a cover by at most $\ell$ cliques can be shrunk to a partition, since subsets of cliques are cliques.

## Sources

- Richard M. Karp, "Reducibility among combinatorial problems", in Raymond E. Miller and James W. Thatcher (eds.), *Complexity of Computer Computations*, Plenum Press, 1972, 85–103, the reduction CHROMATIC NUMBER ∝ CLIQUE COVER. Reprinted in Michael Jünger et al. (eds.), *50 Years of Integer Programming 1958–2008*, Springer, 2010, chapter 8, 219–241.
