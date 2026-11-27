# Length bound for a list in the second field of a decoded pair

Let $\alpha$ and $\beta$ be types with canonical bit-string encodings, and use the canonical codes of lists and
pairs (see [decoded list length](decoded-list-length-le.md) and [decoded pair parts](decoded-pair-parts.md)).
For every bit string $x$, if the decoder of pairs (element of $\alpha$, list over $\beta$) returns
$(a, (b_1, \ldots, b_k))$ on $x$, then $k \le |x|$.
