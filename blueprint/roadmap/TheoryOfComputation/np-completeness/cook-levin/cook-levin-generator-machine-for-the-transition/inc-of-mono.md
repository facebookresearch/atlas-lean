# Increasing literal sequences

Let $f$ assign to each $j \in \mathbb{N}$ a literal
$f(j) = (p_j, b_j)$ with position $p_j \in \mathbb{N}$, and let $m, V \in \mathbb{N}$. Suppose
$p_j < p_{j+1}$ whenever $j + 1 < m$, and $p_j < V$ when $j + 1 = m$. Then for all
$n, a, \mathit{lo} \in \mathbb{N}$ with $a + n = m$ such that $\mathit{lo} \le V$ if $n = 0$ and
$\mathit{lo} \le p_a$ if $n > 0$, the list $f(a), f(a + 1), \dots, f(a + n - 1)$ has increasing
literal positions from $\mathit{lo}$ below $V$.
