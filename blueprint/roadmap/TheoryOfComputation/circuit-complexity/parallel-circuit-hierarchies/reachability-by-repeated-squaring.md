# Reachability by repeated Boolean matrix squaring

The Boolean square of an $N\times N$ Boolean matrix is computed by an unbounded fan-in circuit of depth two with $N^2(N+1)$ gates: entry $(i,j)$ is $\bigvee_k(a_{ik}\wedge a_{kj})$. Composing $t$ copies gives a circuit of depth $2t$ and $tN^2(N+1)$ gates whose entry $(i,j)$ records the existence of a walk of length exactly $2^t$. With self-loops added and $t=\lceil\log_2 N\rceil$ this decides directed reachability; hence $\mathrm{REACH}\in\mathsf{AC}^1$ and $\mathsf{NL}\subseteq\mathsf{AC}^1$ nonuniformly.

## Proof sketch

Squaring the adjacency matrix with self-loops doubles the length of walks represented; $\lceil\log_2 N\rceil$ squarings cover all paths of length below $N$. For $\mathsf{NL}$, the adjacency matrix of the polynomial-size configuration graph of a log-space machine on an input of length $n$ is computed from the input by a depth-one circuit layer (each entry is a constant or an input literal, since a transition reads one input bit), and reachability from the start to the accepting configuration is then decided as above.

## Depends on

- [The AC, TC and AC[q] hierarchies](ac-tc-and-acq-hierarchies.md)
- [The complexity class NL](../../complexity-classes/time-and-space-complexity-classes/nl.md)

## Sources

- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
