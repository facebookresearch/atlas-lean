# Master theorem, toll-dominant case

Let $T$ satisfy a one-term Akra-Bazzi recurrence $T(n) = a\,T(r(n)) + g(n)$ with $r(n) \approx n/b$, $b > 1$ and $g(x) = \Theta(x^c)$ for some $c \ge 0$. If $\log_b a < c$, then $T(n) = \Theta(n^c)$.
