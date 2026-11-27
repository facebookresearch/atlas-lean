# Local tests as constraint graphs

Let $T$ be a local test with positions $P$, alphabet $\Gamma$, random strings $R$ and query set $Q$. Its constraint graph $G_T$ has a vertex for every position (labelled in $\Gamma$) and a vertex for every random string $r$ (labelled in $\Gamma^Q$, the symbols $T$ is claimed to read on $r$); for every $r$ and $i \in Q$ there is an edge between $r$ and $\mathrm{query}(r,i)$ that is satisfied when the claimed tuple makes $D_r$ accept and its $i$-th entry equals the label of the position. Then $G_T$ is satisfiable iff some proof passes $T$ with probability $1$, and every labelling $\sigma$ violates at least a $\big(1 - \mathrm{acc}_T(\pi_\sigma)\big)/|Q|$ fraction of the edges, where $\pi_\sigma$ is the proof read off the position vertices. Hence $\mathrm{UNSAT}(G_T) \ge \big(1 - \max_\pi \mathrm{acc}_T(\pi)\big)/|Q|$.

## Proof sketch

On a random string where the proof read from the positions is rejected, either the claimed tuple is rejected (all $|Q|$ edges of $r$ fail) or it differs from the proof at some query (that edge fails). Averaging over $r$ gives the bound.

## Depends on

- [Local test on a proof string](local-test-on-a-proof-string.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM 54(3), 2007.
