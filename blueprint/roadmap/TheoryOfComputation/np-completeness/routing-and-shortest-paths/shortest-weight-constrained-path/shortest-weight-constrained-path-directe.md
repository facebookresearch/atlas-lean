# Feasible instances of SHORTEST WEIGHT-CONSTRAINED PATH for directed graphs

An instance $(n, A, s, t, K, W)$ of SHORTEST WEIGHT-CONSTRAINED PATH for directed graphs is feasible when there is a list $p = (p_0, \dots, p_r)$ of natural numbers with no repeated entry such that

- $p_0 = s$ and $p_r = t$;
- for every $j < r$ some entry of $A$ has tail $p_j$ and head $p_{j+1}$;
- the total weight $\sum_{j < r} w(p_j, p_{j+1})$ is at most $W$ and the total length $\sum_{j < r} l(p_j, p_{j+1})$ is at most $K$, where $(l(a, b), w(a, b))$ is the [length and weight of the arc from $a$ to $b$](arc-data.md), taken from the first entry of $A$ with tail $a$ and head $b$.

The entries of $p$ are natural labels, not checked against $n$: with $n = 0$, $s = t = 0$ and no arcs, the one-entry list $[0]$ is a witness of total length and weight $0$. For a [well-formed](well-formed.md) instance, $p$ is a simple directed path from $s$ to $t$ in the directed graph on $\{0, \dots, n - 1\}$, and each arc has a single entry. Feasibility does not include well-formedness; the decision problem requires both.
