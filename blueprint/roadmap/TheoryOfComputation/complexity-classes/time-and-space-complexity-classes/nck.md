# The class NC^k

For a natural number $k$, a decision problem $L$ is in $\mathsf{NC}^k$
when there are a constant $c$, a polynomial $p$ with natural number coefficients and a
log-space uniform family of flat Boolean circuits $(C_n)_{n \in \mathbb{N}}$, where $C_n$ has
$n$ inputs, such that for every $n$ the circuit $C_n$ is well formed, has no $\mathrm{mod}$
gates, has at most two inputs at every and gate and every or gate, has at most $p(n)$ gates,
has depth at most $c \cdot (\lfloor \log_2 (n + 1) \rfloor + 1)^k$, and, for every bitstring
$x$ of length $n$, $L$ accepts $x$ exactly when $C_n$ has a last gate and that gate evaluates
to true on input $x$.

So $\mathsf{NC}^k$ consists of the problems decided by log-space uniform circuit families of
polynomial size, fan-in at most $2$ and depth $O(\log^k n)$, and $\mathsf{NC}^0$ is constant
depth. Bounded fan-in is essential: with unbounded fan-in this would be $\mathsf{AC}^k$.

## Sources

- S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Definition 6.21; M. Sipser, Introduction to the Theory of Computation, 3rd ed., 2013, Definition 9.20.
