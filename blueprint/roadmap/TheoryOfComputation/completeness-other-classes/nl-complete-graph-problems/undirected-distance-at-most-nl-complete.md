# Undirected distance at most K is NL-complete

The language $\{\langle G,s,t,K\rangle : G$ undirected, $K\in\mathbb{N}$ in binary, $\mathrm{dist}_G(s,t)\le K\}$ (equivalently, some $s$–$t$ path has at most $K$ edges) is $\mathsf{NL}$-complete under logarithmic-space many-one reductions, although plain undirected connectivity is in $\mathsf{L}$.

## Proof sketch

Membership: it is a special case of bounded directed connectivity on the symmetric digraph. Hardness: reduce STCON on an $n$-vertex digraph to the layered undirected graph with vertices $(v,i)$, $0\le i\le n$, and edges $\{(u,i),(v,i+1)\}$ for arcs $uv$ and $\{(v,i),(v,i+1)\}$; then $t$ is reachable from $s$ iff $\mathrm{dist}((s,0),(t,n))\le n$, since every path of length $n$ must climb one layer per edge.

## Depends on

- [Undirected s-t connectivity as a decision problem](../../polynomial-time-problems/undirected-s-t-connectivity/ustcon-dec.md)
- [The complexity class NL](../../complexity-classes/time-and-space-complexity-classes/nl.md)
- [Log-space many-one reductions](../../complexity-classes/time-and-space-complexity-classes/log-space-red.md)

## Proof depends on

- [Length-bounded directed s–t connectivity is in NL](bounded-stcon-in-nl.md)
- [ST-connectivity is NL-complete](../directed-s-t-connectivity/stcon-nl-complete.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 5.24.
