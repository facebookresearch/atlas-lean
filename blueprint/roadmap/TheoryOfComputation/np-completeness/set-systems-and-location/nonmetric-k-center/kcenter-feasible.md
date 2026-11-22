# Feasible k-center instances

Let $(D, K, B)$ be a k-center instance with rows
$D_0, \dots, D_{m-1}$, and let $n$ be the length of $D_0$, with $n = 0$ if $m = 0$. For $c < m$
and a natural number $f$, write $D_c(f)$ for the entry of $D_c$ at position $f$, counting from
$0$, and set $D_c(f) = 0$ if $D_c$ has at most $f$ entries. The instance is feasible when there
is a set $S$ of at most $K$ locations $f < n$ such that every client $c < m$ has some $f \in S$
with $D_c(f) \le B$.
