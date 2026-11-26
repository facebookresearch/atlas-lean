# Length and weight of an edge in SHORTEST WEIGHT-CONSTRAINED PATH

For an instance of SHORTEST WEIGHT-CONSTRAINED PATH and natural numbers $a$ and $b$, the length and weight of the edge joining $a$ and $b$ is the pair $(l, w)$ of the first entry $(u, v, l, w)$ of the edge list, in list order, with $(u, v) = (a, b)$ or $(u, v) = (b, a)$: either orientation matches. When no entry joins $a$ and $b$, the pair is $(0, 0)$. In a [well-formed](well-formed-2.md) instance at most one entry joins them.
