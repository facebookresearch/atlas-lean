# Stages of degree $n$ of the S-construction

Let $C$ be a category with a zero object and a Waldhausen structure without gluing, and let $n$ be a natural number. A functor $A$ from the [category of intervals](../../not-yet-classified/stable-infinity-sconstruction/interval-category.md) $\mathrm{Ar}[n]$ to $C$ is a stage of degree $n$ when:

- every diagonal value $A(i, i)$ is a zero object of $C$, not necessarily the chosen one;
- for all $i \le j \le k$ in $[n] = \{0, \dots, n\}$, equal indices allowed, the morphisms $A(i, j) \to A(i, k) \to A(j, k)$ that $A$ assigns to [moving the right endpoint](horiz.md) and then [the left endpoint](vert.md) form a cofibration sequence.

So $A(i, j) \to A(i, k)$ is a cofibration with cofiber $A(j, k)$.

## Sources

- F. Waldhausen, *Algebraic K-theory of spaces*, in *Algebraic and Geometric Topology (New Brunswick, 1983)*, Lecture Notes in Mathematics 1126, Springer, 1985, 318–419.
