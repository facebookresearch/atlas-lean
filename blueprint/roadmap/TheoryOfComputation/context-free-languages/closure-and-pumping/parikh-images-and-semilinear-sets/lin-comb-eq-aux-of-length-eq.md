# Unguarded linear combination agrees on equal lengths

Let $T$ be a set, let $p_1, \dots, p_k : T \to \mathbb{N}$ be a list of period vectors and $c_1, \dots, c_m$ a
list of natural numbers with $k = m$. Then the linear combination of the two lists (defined as
$\sum_i c_i p_i$ when the lengths agree and $0$ otherwise) equals the position-wise sum $\sum_{i=1}^{k} c_i
p_i$ computed without checking lengths (which, for lists of different lengths, would stop at the end of the
shorter one).

## Sources

- R. J. Parikh, "On context-free languages", *Journal of the ACM* 13 (1966), 570–581.
