# Feasible EXTERNAL MACRO DATA COMPRESSION with a fixed alphabet and logarithmic pointer cost instances

$s$ has an external macro compression within the bound $B$ with pointer parameter $c = \lceil h \log_2 |s| \rceil$. Each pointer occurrence counts once in the string lengths and then adds $c - 1$ in natural-number subtraction, so its effective charge is $\max(1, c)$: for a one-symbol word $c = 0$, yet each occurrence still costs $1$. The parameter handed to the compression predicate is $c$, not the per-occurrence charge.
