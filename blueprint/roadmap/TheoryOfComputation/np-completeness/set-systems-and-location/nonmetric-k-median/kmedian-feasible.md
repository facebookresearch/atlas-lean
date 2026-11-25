# Feasible k-median instances

Let $(d, K, B)$ be a k-median instance whose cost matrix $d$
has rows $d_0, \dots, d_{n-1}$, one per client, and let $m$ be the length of $d_0$, or $m = 0$
when $n = 0$. The instance is feasible when there are a set $S \subseteq \{0, \dots, m-1\}$ of at
most $K$ locations and a choice of $a(c) \in S$ for each client $c < n$ such that
$\sum_{c < n} d_c(a(c)) \le B$, where $d_c(j)$ is the entry of $d_c$ at index $j$ (counting from
$0$), read as $0$ when $d_c$ has fewer than $j + 1$ entries.
