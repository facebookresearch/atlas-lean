# Feasible CONSISTENT 2-TERM DNF instances

An instance $(n, P, N)$ of CONSISTENT 2-TERM DNF is feasible when some DNF formula with at most two terms, every literal of which is a variable $x_k$ with $k < n$ or its negation, is true on every example in $P$ and false on every example in $N$; an example $(e_0, e_1, \dots)$ assigns $e_k$ to $x_k$. If an example has no entry at position $k$, it assigns false to $x_k$. Entries at positions $k \ge n$ cannot affect feasibility, since literals use only indices below $n$.
