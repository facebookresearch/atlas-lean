# Length bound for the middle list of a decoded triple

Let $\alpha$, $\beta$ and $\gamma$ be types with canonical bit-string encodings, and use the canonical codes of
lists and pairs (see [decoded list length](decoded-list-length-le.md) and [decoded pair
parts](decoded-pair-parts.md)); a triple $(a, bs, c)$ is the pair $(a, (bs, c))$. For every bit string $x$, if the
decoder of triples (element of $\alpha$, list over $\beta$, element of $\gamma$) returns
$(a, (b_1, \ldots, b_k), c)$ on $x$, then $k \le |x|$.

This bounds, for instance, the rows of a distance matrix or the sets of a set-cover instance by the input length.
