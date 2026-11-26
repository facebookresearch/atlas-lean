# Step count of the main loop

Write $0$ for false, $1$ for true, and $xyr$ for the bit
string whose first two bits are $x, y$ followed by $r$. For a bit string $l$, a flag $\iota$
(whether a clause is open) and natural numbers $n, k, m$, let $c = n + 1$ if $\iota$ is true and
$c = 0$ otherwise. The step count $T(l, \iota, n, k, m)$ is defined by recursion on $l$:
$T(00r, \iota, n, k, m) = 2 + c + (k + 1) + T(r, 1, 0, 0, m + 1)$;
$T(10r, \iota, n, k, m) = 2 + T(r, \iota, n, k + 1, m)$;
for every bit $s$, $T(s1r, \iota, n, k, m)$ is $2 + 2(k + 1) + T(r, 1, n + 1, k + 1, m)$ if $\iota$
is true and $2 + T(r, 0, n, k, m)$ otherwise; on a one-bit string $T = 2 + (k + 1) + c + (m + 1)$;
and on the empty string $T = 1 + (k + 1) + c + (m + 1)$.
