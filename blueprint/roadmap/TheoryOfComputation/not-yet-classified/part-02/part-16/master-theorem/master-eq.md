# Master theorem, critical case

Let $T$ satisfy the recurrence with $a$ subproblems of size $n/b$, $b > 1$, and toll $g(x) = \Theta(x^c)$ with $c \ge 0$. If $c = \log_b a$, then $T(n) = \Theta(n^c \log n)$; this includes $c = 0$, $a = 1$.
