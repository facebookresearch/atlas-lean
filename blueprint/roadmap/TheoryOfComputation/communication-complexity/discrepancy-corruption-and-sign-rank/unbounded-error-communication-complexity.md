# Unbounded-error communication complexity

A private-coin protocol computes $f$ with *unbounded error* if on every input pair its output is correct with probability strictly greater than $1/2$. The *unbounded-error communication complexity* $\mathrm{UPP}(f)$ is the least cost of such a protocol, over all numbers of private random bits. Since the random strings are finite, every unbounded-error protocol has error at most some $\varepsilon < 1/2$, so $\mathrm{UPP}(f) = \inf_{\varepsilon < 1/2} R^{\mathrm{priv}}_\varepsilon(f) \le D(f)$.

## Depends on

- [Randomized communication complexity](../randomized-communication-protocols/rand-complexity.md)
- [Newman's theorem](../randomized-communication-protocols/newman-private-coins.md)

## Sources

- R. Paturi and J. Simon, "Probabilistic Communication Complexity", Journal of Computer and System Sciences 33(1), 1986.
