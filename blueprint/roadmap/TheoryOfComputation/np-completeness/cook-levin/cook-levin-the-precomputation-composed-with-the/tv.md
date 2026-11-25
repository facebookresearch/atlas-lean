# Target counter values

For a polynomial $k$ with natural-number coefficients and natural
numbers $c, e, d, n$, let $m = n + 1 + k(n)$, $T = (m + c)^e$ and let $H = m + (T + 1)d + 1$ be
the stack cap. The target values on the twelve target counters assign $T$ to each of
$u_T, s_T, h_T, a_T, i_T$, assign $H$ to each of $u_H, s_H, h_H, a_H$, and assign $n + 1$ to
$i_X$, $k(n)$ to $i_E$ and $(T + 1)d + 1$ to $i_F$.

In particular the value at $i_F$ is $H - m$.
