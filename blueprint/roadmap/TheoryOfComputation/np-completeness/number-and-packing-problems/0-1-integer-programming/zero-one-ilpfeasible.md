# Feasible 0-1 integer programs

Let $(n, A, b)$ be a 0-1 integer programming instance whose
coefficient matrix has the rows $A_0, \dots, A_{m-1}$, with list entries indexed from $0$. For
$r < m$ and $j < n$, let $a_{rj}$ be the integer $p - q$ if row $A_r$ has a $j$-th entry
$(p, q)$, and $a_{rj} = 0$ otherwise; let $b_r$ be the integer $p' - q'$ if $b$ has an $r$-th
entry $(p', q')$, and $b_r = 0$ otherwise. The instance is feasible when there is
$x \in \{0, 1\}^n$ such that $\sum_{j < n} a_{rj} x_j \le b_r$ in $\mathbb{Z}$ for every $r < m$.
