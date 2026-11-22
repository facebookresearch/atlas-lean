# Entry bound for a converted tensor instance

Let $N$ be a factored tensor network on a finite linearly ordered vertex set $J$ with size
parameters $P, B$, and for each pair $a, b$ let $D_{a,b}$ be a finite set of names and
$\delta_{a,b}$ a map from names to labels of $N$. Then every entry of the complete-graph instance
of $N$ built from $D$ and $\delta$ satisfies $|R_a(\theta)| \le 2^{P + B |J|}$, where $|J|$ is
the number of vertices.

Each entry is a sum of at most $2^P$ terms, each a weight times $|J| - 1$ factors.
