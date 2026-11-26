# Length bound for a list in the first field of a decoded pair

Let $\alpha$ and $\beta$ be types with canonical bit-string encodings, and use the canonical codes of lists and
pairs (see [decoded list length](decoded-list-length-le.md) and [decoded pair parts](decoded-pair-parts.md)).
For every bit string $x$, if the decoder of pairs (list over $\alpha$, element of $\beta$) returns
$((a_1, \ldots, a_k), b)$ on $x$, then $k \le |x|$.
