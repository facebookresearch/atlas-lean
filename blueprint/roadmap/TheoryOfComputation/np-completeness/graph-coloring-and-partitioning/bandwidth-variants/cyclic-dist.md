# Distance on a cycle of positions

For natural numbers $n$, $a$ and $b$, the cyclic distance between $a$ and $b$ on $n$ positions is $\min(d, n - d)$ with $d = |(a \bmod n) - (b \bmod n)|$ and truncated subtraction; for $a, b < n$ this is the shorter way around the cycle $0, \dots, n-1$. With $n = 0$ the residues are $a$ and $b$ themselves and the value is $0$.
