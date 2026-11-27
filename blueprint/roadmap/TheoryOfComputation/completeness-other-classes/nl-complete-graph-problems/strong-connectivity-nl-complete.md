# Strong connectivity of digraphs is NL-complete

$\mathrm{SC}=\{G : G$ a finite digraph (loops allowed) in which every vertex reaches every other$\}$ is $\mathsf{NL}$-complete under logspace many-one reductions; the digraph with no vertices is strongly connected.

## Proof sketch

Membership: for every ordered pair $(u,v)$ guess a path, keeping only two loop counters and the current vertex; rejection on any failure is fine because nondeterminism is existential over all paths simultaneously. Hardness: from $\langle G,s,t\rangle$ build $G'$ by adding arcs from every vertex to $s$ and from $t$ to every vertex; $G'$ is strongly connected iff $t$ is reachable from $s$ in $G$.

## Depends on

- [The complexity class NL](../../complexity-classes/time-and-space-complexity-classes/nl.md)
- [Log-space many-one reductions](../../complexity-classes/time-and-space-complexity-classes/log-space-red.md)

## Proof depends on

- [ST-connectivity is NL-complete](../directed-s-t-connectivity/stcon-nl-complete.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 4, Exercise 4.
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 5.23.
