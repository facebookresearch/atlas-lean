# Randomized non-adaptive reductions to approximating Kolmogorov complexity

Any computable language with an honest randomized polynomial-time non-adaptive reduction to approximating Kolmogorov complexity within an additive $\omega(\log n)$ lies in $\mathsf{AM}\cap\mathsf{coAM}$, while every $\mathsf{NEXP}$ language reduces this way to $O(\log n)$-approximation.

Kolmogorov complexity is treated as a functional oracle: on query $q$ it returns $K(q)$. An oracle $O$ is a $\beta$-additive approximation of $K$ if $|O(q)-K(q)|\le\beta(|q|)$ for every $q$, and a reduction to $\beta$-approximating $K$ must be correct with every such oracle; for $\beta=\omega(1)$ this is robust to the choice of universal machine and for $\beta=O(\log n)$ to the prefix-free variant. A reduction is polynomially honest if every query on input $x$ has length $|x|^{\Omega(1)}$, and has advantage $\epsilon$ if it is correct with probability at least $1/2+\epsilon$.

1. If a computable language $L$ has a randomized polynomial-time non-adaptive reduction $F$ to $\omega(\log n)$-additively approximating $K$ that is polynomially honest and has inverse-polynomial advantage, then $L\in\mathsf{AM}\cap\mathsf{coAM}$.
2. Every $L\in\mathsf{NEXP}$ has a polynomially honest randomized polynomial-time non-adaptive reduction with constant advantage to $O(\log n)$-additively approximating $K$.
3. If there is a polynomially honest randomized polynomial-time non-adaptive reduction from SAT to $\omega(\log n)$-additively approximating $K$, then the polynomial hierarchy collapses.
4. If a computable $L$ has a polynomially honest randomized polynomial-time non-adaptive reduction to avoiding the range of a computable hitting set generator with seed length $n-\omega(\log n)$, then $L\in\mathsf{AM}\cap\mathsf{coAM}$.

The previous best upper bound for languages reducible to $\omega(\log n)$-approximation was $\mathsf{EXPSPACE}$; with adaptive queries, approximating $K$ even within a factor $|q|^{1-\epsilon}$ is hard for $\mathsf{PSPACE}$.

## Expansion

Fix the reduction $M$ and an input $x$, let $\pi(q)$ be the probability over the reduction's randomness and a random query index that $q$ is the query asked, and use the context-sensitive oracle $J^M_x(q)=\lceil\log 1/\pi(q)\rceil$, which is $\beta$-close to $K(q)$ for all but a small fraction of queries. For every sufficiently long $x$ one builds a context-insensitive $\beta$-approximation $K'$ of $K$ that agrees with $J$ on all queries of most runs, so $M^J$ computes $L$ with advantage $\epsilon/2$; the argument picks the first failing $x$, which has low Kolmogorov complexity, and honesty ties $|x|$ to the query lengths. Each value of $J$ is an approximate counting problem, solvable in $\mathsf{AM}\cap\mathsf{coAM}$; to make Merlin's answers consistent, a random shift $J[\gamma]$ with $\gamma\in[0,1)$ is used, and for a random $\gamma$ the computation $M^{J[\gamma]}$ is simulated in $\mathsf{AM}\cap\mathsf{coAM}$. Item 2 is due to Hirahara, item 3 follows from item 1 because $\mathsf{SAT}\in\mathsf{AM}\cap\mathsf{coAM}$ collapses $\mathsf{PH}$, and item 4 holds because a Kolmogorov oracle avoids the range of any computable hitting set generator.

## Depends on

- [Kolmogorov complexity](../../../kolmogorov-complexity/k.md)
- [The class AM (Arthur–Merlin)](../../../complexity-classes/time-and-space-complexity-classes/am.md)

## Proof depends on

None.

## Sources

- Michael Saks and Rahul Santhanam, "On Randomized Reductions to the Random Strings", *37th Computational Complexity Conference (CCC 2022)*, LIPIcs, 2022, https://doi.org/10.4230/LIPIcs.CCC.2022.29 (Theorem 3 with Corollaries 4 and 5, Section 1.1.1, proof overview in Section 1.2).
