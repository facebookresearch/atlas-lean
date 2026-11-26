# Razborov's hard distribution for disjointness is corrupted

On $2m + 1$ points, draw a uniform partition into a point $i$ and two $m$-sets $T_x, T_y$, uniform subsets $x \subseteq T_x$, $y \subseteq T_y$, and output either the disjoint pair $(x, y)$ or, with probability $1/2$, the intersecting pair $(x \cup \{i\}, y \cup \{i\})$. Under this distribution disjointness is $(\alpha, 2^{-\Omega(m)})$-corrupted on the answer "disjoint" for an absolute constant $\alpha > 0$: every rectangle with substantial mass on disjoint pairs has a constant fraction of its mass on intersecting pairs. Consequently $R_{1/3}(\mathrm{DISJ}_n) = \Omega(n)$.

## Proof sketch

For a rectangle $A \times B$, condition on the partition; the events "$x \cup\{i\} \in A$" and "$y \cup \{i\} \in B$" are compared with "$x \in A$", "$y \in B$" through a sampling lemma showing that for most partitions adding $i$ does not drop the conditional probabilities by more than a constant factor unless the rectangle is tiny.

## Depends on

- [Set intersection function](../randomized-communication-protocols/disj-fn.md)
- [The corruption (rectangle) bound](the-corruption-bound.md)

## Sources

- A. A. Razborov, "On the Distributional Complexity of Disjointness", Theoretical Computer Science 106(2), 1992.
- B. Kalyanasundaram and G. Schnitger, "The Probabilistic Communication Complexity of Set Intersection", SIAM Journal on Discrete Mathematics 5(4), 1992.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
