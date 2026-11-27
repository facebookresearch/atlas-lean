# Unbounded-error communication complexity

Let $X$ and $Y$ be finite. A private-coin protocol computes $f : X \times Y \to \{0,1\}$ with *unbounded error* if on every input pair its output is correct with probability strictly greater than $1/2$, the probability being over the players' private random strings drawn uniformly from finite sets. The *unbounded-error communication complexity* $\mathrm{UPP}(f)$ is the least cost of such a protocol, over all finite sets of private random strings. Since the inputs and random strings are finite, every unbounded-error protocol has error at most some $\varepsilon < 1/2$, so $\mathrm{UPP}(f) = \min_{\varepsilon < 1/2} R^{\mathrm{priv}}_\varepsilon(f) \le D(f)$, where $R^{\mathrm{priv}}_\varepsilon(f)$ is the least cost of a private-coin protocol whose error probability is at most $\varepsilon$ on every input.

## Depends on

- [Error probability of a private-coin protocol](../randomized-communication-protocols/private-error-prob.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Sources

- R. Paturi and J. Simon, "Probabilistic Communication Complexity", Journal of Computer and System Sciences 33(1), 1986.
