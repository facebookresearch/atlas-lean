# Padding a string to a given length

For a natural number $n$ and a binary string $p$, the
padding of $p$ to length $n$ is the string $0^k 1 p$ with $k = \max(n - 1 - |p|, 0)$; when
$|p| < n$ it has length $n$.
