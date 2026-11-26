# Feasible instances of SHORTEST PATH WITH FORBIDDEN PAIRS

An instance $(n, E, C, s, f, K)$ of SHORTEST PATH WITH FORBIDDEN PAIRS is feasible when there is a list $p$ of natural numbers with no repeated entry such that

- $p$ starts with $s$ and ends with $f$;
- every two consecutive entries $u, v$ of $p$ are listed in $E$ as $(u, v)$ or as $(v, u)$;
- for every pair $(a, b)$ in $C$ with $a \ne b$, at most one of $a$ and $b$ occurs in $p$;
- $p$ has at most $K + 1$ entries, that is, at most $K$ edges.

The entries of $p$ are natural labels, not checked against $n$: with $n = 0$, $s = f = 0$ and no edges, the one-entry list $[0]$ is a witness with zero edges. For a [well-formed](well-formed.md) instance, $p$ is a simple path from $s$ to $f$ in the graph on $\{0, \dots, n - 1\}$ with at most $K$ edges that contains at most one vertex from each pair in $C$. Feasibility does not include well-formedness; the decision problem requires both.
