# Optimality (the invariance theorem)

Let $D$ be a partial recursive function from binary
strings to binary strings, viewed as a description method. Then there is a natural number $c$
such that for all binary strings $x$ and $p$ for which $D(p)$ is defined and equals $x$, the
Kolmogorov complexity of $x$ satisfies $K(x) \le |p| + c$, where $|p|$ is the length of $p$.
