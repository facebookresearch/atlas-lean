# Constant-gap reductions to constraint graphs give PCP verifiers

Let $\Pi$ be a promise problem and let $\Sigma$ be a fixed finite alphabet. Suppose there are $c > 0$ and a polynomial-time map $x \mapsto G_x$ to binary constraint graphs over $\Sigma$ such that $G_x$ is satisfiable for $x \in \Pi_{\mathrm{yes}}$ and $\mathrm{UNSAT}(G_x) \ge c$ for $x \in \Pi_{\mathrm{no}}$. Then $\Pi \in \mathrm{PromisePCP}(\log n, 1)$; if $\Pi$ is a language, then there are constants $c, c' > 0$ such that $\Pi \in \mathrm{PCP}(c\log n, c')$ with perfect completeness.

## Proof sketch

The verifier constructs $G_x$, runs the random-edge verifier on a proof listing a fixed-width binary encoding of a label per vertex, and repeats it a constant number $k$ of times with $(1 - c/2)^k \le 1/2$ (one additional repetition lowers soundness below $1/3$, and padding the random coins to $c\log n$ bits puts any language $\Pi$ in $\mathrm{PCP}(c\log n, c')$ for constants $c, c' > 0$). Each round uses $O(\log |G_x|) = O(\log n)$ random bits and $O(\log|\Sigma|) = O(1)$ queries.

## Depends on

- [Promise class PCP(r, q)](promise-class-pcp.md)
- [Assignment testers](../pcp-constructions/assignment-testers.md)

## Proof depends on

- [The random-edge verifier rejects with probability at least half the gap](random-edge-verifier-soundness.md)
- [Independent repetition multiplies acceptance probabilities](independent-repetition-of-local-tests.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM 54(3), 2007.
