# The symbolic effect grows by at most the number of stack operations

Let $q$ be a statement
tree, let $W$ assign to each stack a window (a list of cells, each a symbol or $\bot$), and let
$n(q)$ be the largest number of push, peek and pop nodes on a root-to-leaf path of $q$. For every
state $v$, pushed lists $P$ and consumption counts $c$, the pushed lists $P'$ and consumption
counts $c'$ of the symbolic effect of $q$ on $W$ from $v$, $P$, $c$ satisfy
$|P'_k| \le |P_k| + n(q)$ and $c'_k \le c_k + n(q)$ for every stack $k$.
