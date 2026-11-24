# Declared time bound of the SAT verifier

For all lists of Booleans $x$ (the input) and
$w$ (the witness), the declared time cost of the SAT verifier on $(x, w)$ is at most $N^2 + N$,
where $N = |x| + |w|$ is the sum of their lengths.

If $x$ decodes to a formula with $n$ literals, then $n \le N$ and the check costs at most
$n(n + 1) \le N(N + 1)$.
