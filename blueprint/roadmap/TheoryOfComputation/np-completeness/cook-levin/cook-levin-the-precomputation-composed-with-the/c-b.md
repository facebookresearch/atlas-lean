# Step budget of the counter program

For a polynomial $k$ with natural-number coefficients
and natural numbers $c, e, d, n$, let $m = n + 1 + k(n)$, $T = (m + c)^e$ and
$H = m + (T + 1)d + 1$. The step budget of the counter program at $(k, c, e, d, n)$ is

$$
1 + h + (k(n) + 1) + (n + 1) + 2 + (2m + 2) + 3 + p + 1 + (d(2T + 3) + d + 2) + 1 +
(dT + d + 2) + (m + 1) + (T + 1) + (H + 1),
$$

where $h$ is the exact step count of the Horner rounds over the coefficient list of $k$ with
base $n$ from accumulator $0$, and $p = e\left((m + c + 1)^e (3(m + c) + 5) + 5\right) + 1$ is
the step budget of the power loop with $e$ rounds, start value $1$ and base $m + c$.
