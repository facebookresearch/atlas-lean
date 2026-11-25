# Permanent of an encoded 0-1 matrix

For a bitstring $x$ that decodes to a pair $(n, e)$ of
a natural number $n$ and a list $e = (e_0, \dots, e_{m-1})$ of natural numbers with $m = n^2$
and every $e_j \le 1$, the value at $x$ is the permanent
$\sum_{\sigma} \prod_{i < n} e_{in + \sigma(i)}$ of the $n \times n$ matrix with entries $e$ in
row-major order, the sum running over all permutations $\sigma$ of $\{0, \dots, n - 1\}$. For
every other bitstring the value is $0$.
