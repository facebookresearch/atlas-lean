# Cross-examination debate with a stochastic oracle

Let $M$ be a probabilistic oracle machine with a stochastic oracle $O$, running in time $T$ with oracle queries of length $l$, that decides a language $L$: it outputs $1$ with probability at least $2/3$ on every $x \in L$ and at most $1/3$ on every $x \notin L$. For $K > 0$, $M$ is *$K$-Lipschitz at $O$* if $\sup_x \lvert\Pr[M^{O}(x)=1]-\Pr[M^{O'}(x)=1]\rvert \le K \sup_z \lvert\Pr[O(z)=1]-\Pr[O'(z)=1]\rvert$ for every oracle $O'$. If $M$ is $K$-Lipschitz at $O$, there is a debate protocol with cross-examination that decides $L$ with completeness $3/5$ and soundness $2/5$: for $x \in L$ the honest proposer makes the verifier output $1$ with probability at least $3/5$ against every challenger, and for $x \notin L$ the honest challenger keeps that probability at most $2/5$ against every proposer. The honest provers run in time $O(K^2 T \log T)$, and the verifier runs in time $O(K^2 + l \log T)$ and makes $O(K^2)$ oracle queries.

## Proof sketch

Round by round, the proposer announces the conditional probability $\hat p_t$ that the next transcript bit of $M$ is $1$, the two provers jointly flip a shared uniform $z_t$, and the bit is set to $1$ iff $z_t \le \hat p_t$; the challenger may abort at a round where $\hat p_t$ is wrong, and the verifier then estimates the true conditional probability from $O(K^2)$ samples (oracle queries) and rejects the proposer if it differs from $\hat p_t$ by at least $1/(4\lceil150K\rceil)$. A Lipschitz condition bounds how errors propagate, so a false global claim forces a large local discrepancy at some step.

## Depends on

- [The class IP](../../../complexity-classes/time-and-space-complexity-classes/ip.md)

## Sources

- Jonah Brown-Cohen, Geoffrey Irving and Georgios Piliouras, "Scalable AI Safety via Doubly-Efficient Debate", Proceedings of the 41st International Conference on Machine Learning, PMLR 235, 2024 (arXiv:2311.14125), Definition 6.1 (arXiv v1 prints it with a strict inequality, which no machine satisfies at $O'=O$; the proof of Theorem 6.2 uses it only for $O'$ strictly within $1/\lceil150K\rceil$ of $O$, where $\le$ suffices), Figure 1, Theorem 6.2 and Appendix D.
