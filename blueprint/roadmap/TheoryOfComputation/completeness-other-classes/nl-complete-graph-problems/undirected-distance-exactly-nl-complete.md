# Undirected distance exactly K is NL-complete

The language $\{\langle G,s,t,K\rangle : G$ undirected and $\mathrm{dist}_G(s,t)=K\}$ is $\mathsf{NL}$-complete under logspace many-one reductions. (This differs from asking for a simple path with exactly $K$ edges: in a triangle with adjacent terminals there is such a path with $2$ edges but the distance is $1$.)

## Proof sketch

$\mathrm{dist}=K$ iff $\mathrm{dist}\le K$ and not $\mathrm{dist}\le K-1$; both conditions are in $\mathsf{NL}$, the second by closure of $\mathsf{NL}$ under complement, and $\mathsf{NL}$ is closed under intersection. Hardness uses the layered graph of the 'at most' case, in which the distance from $(s,0)$ to $(t,n)$ is at least $n$.

## Depends on

- [Undirected s-t connectivity as a decision problem](../../polynomial-time-problems/undirected-s-t-connectivity/ustcon-dec.md)
- [The complexity class NL](../../complexity-classes/time-and-space-complexity-classes/nl.md)

## Proof depends on

- [Undirected distance at most K is NL-complete](undirected-distance-at-most-nl-complete.md)
- [Immerman-Szelepcsenyi theorem: NL = coNL](../../complexity-classes/immerman-szelepcsenyi.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 5.24.
