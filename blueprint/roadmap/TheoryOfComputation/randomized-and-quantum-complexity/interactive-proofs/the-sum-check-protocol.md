# The sum-check protocol

Let $g$ be a polynomial in $m$ variables over a finite field $\mathbb{F}$ with degree at most $d$ in each variable, and $K \in \mathbb{F}$. The sum-check protocol is an $m$-round interactive proof for the claim $\sum_{x \in \{0,1\}^m} g(x) = K$: in round $i$ the prover sends a univariate polynomial $g_i(X)$ of degree at most $d$, claimed to equal $\sum_{x_{i+1}, \dots, x_m \in \{0,1\}} g(r_1, \dots, r_{i-1}, X, x_{i+1}, \dots, x_m)$; the verifier checks the degree and $g_i(0) + g_i(1) = g_{i-1}(r_{i-1})$ (with $g_0(r_0) = K$) and sends a uniformly random $r_i \in \mathbb{F}$; finally it checks $g_m(r_m) = g(r_1, \dots, r_m)$ with one evaluation of $g$. The protocol has perfect completeness and soundness error at most $md/|\mathbb{F}|$.

## Depends on

- [The class IP](../../complexity-classes/time-and-space-complexity-classes/ip.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- One-variable completeness and root-count soundness (existing code without pages, backfill referral) (proof prerequisite; formal statement exists, page pending)
- A nonzero univariate polynomial of degree at most d has at most d roots (proof prerequisite; formal statement exists, page pending)

## Sources

- C. Lund, L. Fortnow, H. Karloff and N. Nisan, "Algebraic methods for interactive proof systems", *Journal of the ACM* 39(4):859–868, 1992, <https://lance.fortnow.com/papers/files/ip.pdf>
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009
