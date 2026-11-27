# Even cardinality is not first-order definable

No first-order sentence over the empty signature holds in exactly the finite sets of even cardinality, and no first-order sentence over the signature $\{<\}$
holds in exactly the finite linear orders of even length.

Over the empty signature, the Duplicator wins the $k$-round game on sets of $k$ and $k + 1$ elements by answering each newly played element with a new element
and each repeated element with its earlier partner, so the two sets satisfy the same sentences of quantifier rank at most $k$. Over linear orders, any two finite
linear orders of length at least $2^k$, such as those of lengths $2^k$ and $2^k + 1$, satisfy the same sentences of quantifier rank at most $k$. In both cases one
structure of each pair has even size and the other odd size, so a defining sentence of quantifier rank $k$ would separate them.

## Proof depends on

- [Ehrenfeucht–Fraïssé theorem](ehrenfeuchtfraisse-theorem.md)
- [EF games on finite linear orders: the $2^n - 1$ threshold](../ehrenfeucht-fraisse-games/ef-games-on-finite-linear-orders.md)

## Sources

- L. Libkin, *Elements of Finite Model Theory*, Springer, 2004 (author copy), <https://www.cs.utoronto.ca/~libkin/fmt/fmt.pdf>: Corollary 3.11 and the following paragraph (the empty signature), Theorem 3.6 (linear orders of length at least $2^k$) and Corollary 3.12 (even is not first-order expressible over linear orders).
