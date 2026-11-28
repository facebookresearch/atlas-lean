# Length and weight of an arc in SHORTEST WEIGHT-CONSTRAINED PATH for directed graphs

For an instance of SHORTEST WEIGHT-CONSTRAINED PATH for directed graphs and natural numbers $a$ and $b$, the length and weight of the arc from $a$ to $b$ is the pair $(l, w)$ of the first entry $(a, b, l, w)$ of the arc list, in list order. Only the direction from $a$ to $b$ matches: an entry $(b, a, l, w)$ does not. When no entry has tail $a$ and head $b$, the pair is $(0, 0)$. In a [well-formed](well-formed.md) instance at most one entry has tail $a$ and head $b$.
