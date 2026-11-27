# The square through the diagonal is a pushout

Let $C$ be a category with a zero object and a Waldhausen structure without gluing, and let $A$ be a [stage of degree $n$](is-stage.md). For all $i \le j \le k$ in $[n] = \{0, \dots, n\}$, equal indices allowed, the square formed by the morphisms that $A$ assigns to

$$
(i, j) \to (i, k), \qquad (i, j) \to (j, j), \qquad (i, k) \to (j, k), \qquad (j, j) \to (j, k)
$$

is a pushout square: $A(j, k)$ is a pushout of $A(i, k) \leftarrow A(i, j) \to A(j, j)$, where $A(j, j)$ is a zero object.
