# Permanent of an encoded 0-1 matrix

For a bitstring $x$: if $x$ decodes, under the
canonical bitstring encoding, to a pair $(n, e)$ of a natural number $n$ and a list
$e = (e_0, \dots, e_{n^2 - 1})$ of $n^2$ natural numbers each at most $1$, the value at $x$ is the
permanent $\sum_{\sigma} \prod_{i=0}^{n-1} e_{in + \sigma(i)}$ of the $n \times n$ matrix with
row-major entries $e$, where $\sigma$ ranges over the permutations of $\{0, \dots, n - 1\}$;
otherwise the value is $0$.
