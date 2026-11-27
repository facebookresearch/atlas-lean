# Length-bounded directed s–t connectivity is in NL

Let $\mathrm{BoundedSTCON}=\{\langle G,s,t,k\rangle : G$ a directed graph given by its adjacency matrix, $k\in\mathbb{N}$ in binary, and there is a directed walk from $s$ to $t$ with at most $k$ arcs$\}$ (zero-length walks allowed). Then $\mathrm{BoundedSTCON}\in\mathsf{NL}$; indeed it logspace-reduces to STCON via a layered graph with $\min(k,n)+1$ layers.

## Proof sketch

Guess the walk vertex by vertex, keeping the current vertex and a step counter capped at $\min(k,n)$, both of $O(\log n)$ bits; walks longer than $n-1$ can be shortened to simple paths.

## Depends on

- [Directed $s$-$t$ connectivity](../directed-s-t-connectivity/stcon-dec.md)
- [The complexity class NL](../../complexity-classes/time-and-space-complexity-classes/nl.md)

## Proof depends on

- [ST-connectivity is NL-complete](../directed-s-t-connectivity/stcon-nl-complete.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 5.19.
