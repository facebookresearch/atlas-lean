# Graph non-isomorphism has a private-coin interactive proof

$\mathrm{GNI}=\{\langle G_0,G_1\rangle : G_0\not\cong G_1\}$ has a two-message private-coin interactive proof with perfect completeness and soundness error $1/2$: the verifier picks $b\in\{0,1\}$ and a uniformly random permutation $\pi$, sends $H=\pi(G_b)$, and accepts iff the prover returns $b$.

## Proof sketch

If $G_0\not\cong G_1$, $H$ determines $b$ and an unbounded prover finds it. If $G_0\cong G_1$, $\pi(G_0)$ and $\pi(G_1)$ are identically distributed, so $b$ is independent of $H$ and any prover guesses it with probability $1/2$.

## Depends on

- [The class IP](../../../complexity-classes/time-and-space-complexity-classes/ip.md)
- [Directed graph non-isomorphism as a decision problem](../../graph-isomorphism-and-arthur-merlin-proofs/graph-non-iso-dec.md)

## Sources

- Oded Goldreich, Silvio Micali and Avi Wigderson, "Proofs that Yield Nothing but Their Validity or All Languages in NP Have Zero-Knowledge Proof Systems", Journal of the ACM 38(3), 690–728, 1991.
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 8.
