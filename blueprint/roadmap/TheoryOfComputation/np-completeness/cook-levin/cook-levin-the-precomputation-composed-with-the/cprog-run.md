# The counter program's run

Let $k$ be a polynomial with natural-number coefficients, let
$c, e, d, n$ be natural numbers, and put $m = n + 1 + k(n)$ and $T = (m + c)^e$. Start the
counter program for $k, c, e, d$ at its first label with any flag, any output stack $o$, the
scratch counter $N$ equal to $n$ and every other counter equal to $0$. Then, in a number of
steps at most the step budget of the counter program at $(k, c, e, d, n)$, it reaches its label
$\mathrm{done}$ with flag false, output stack $o$, and counter values $T$ on the targets
$uT, sT, hT, aT, iT$; $m + (T + 1)d + 1$ on the targets $uH, sH, hH, aH$; $n + 1$ on $iX$;
$k(n)$ on $iE$; $(T + 1)d + 1$ on $iF$; $m + c$ on the scratch counter $B$; $d$ on the scratch
counter $Dd$; and $0$ on every other counter.
