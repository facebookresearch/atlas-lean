# Fooling sets bound the tiling number

Let $S \subseteq X \times Y$ be a fooling set for $f$ with value $z$: $f = z$ on $S$, and for distinct $(x, y), (x', y') \in S$ at least one of $f(x, y') \ne z$, $f(x', y) \ne z$. Then in every labelled rectangle partition for $f$, distinct elements of $S$ lie in distinct rectangles labelled $z$. Hence $|S| \le \chi(f)$ (counting $z$-labelled pieces), and this holds for arbitrary partitions, not only those arising from protocols.

## Proof sketch

If two elements of $S$ lay in one rectangle $A \times B$ with label $z$, the rectangle would also contain the two crossed pairs, on one of which $f \ne z$.

## Depends on

- [Monochromatic rectangle partitions and the tiling number](monochromatic-rectangle-partitions-and-tiling-number.md)
- [Fooling set](../deterministic-communication-protocols/is-fooling-set.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
