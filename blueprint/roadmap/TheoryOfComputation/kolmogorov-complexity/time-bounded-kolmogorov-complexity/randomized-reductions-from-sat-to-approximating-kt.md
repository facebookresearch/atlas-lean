# Randomized reductions from SAT to approximating time-bounded Kolmogorov complexity

If, for a fixed polynomial running time $t'$ and every large enough polynomial $t$, SAT has an honest randomized non-adaptive time-$t'$ reduction to approximating $K^t$ within an additive $\omega(\log m)$, then either $\mathsf{E}$ has non-deterministic circuits of size $2^{o(n)}$ infinitely often or $\mathsf{NE}=\mathsf{coNE}$.

$K^t(x)$ is the length of a shortest program that prints $x$ within $t(|x|)$ steps on a fixed universal machine. Suppose there is a polynomially bounded $t':\mathbb{N}\to\mathbb{N}$ such that for all large enough $t=\mathrm{poly}(t')$ there is a randomized time-$t'$ non-adaptive reduction from SAT to $\omega(\log m)$-additively approximating $K^t$ that is polynomially honest, has fixed query length and has inverse-polynomial advantage. Then either $\mathsf{E}$ has non-deterministic circuits of size $2^{o(n)}$ infinitely often, or $\mathsf{NE}=\mathsf{coNE}$.

Here an oracle $O$ is a $\beta$-additive approximation of $K^t$ if $|O(q)-K^t(q)|\le\beta(|q|)$ for every $q$, and a reduction to $\beta$-approximating $K^t$ must be correct with every such oracle. A reduction is polynomially honest if every query on input $x$ has length $|x|^{\Omega(1)}$, has fixed query length if the length of each query on input $x$ depends only on $|x|$, and has advantage $\epsilon$ if it is correct with probability at least $1/2+\epsilon$.

This appears to be the first negative evidence against $\mathsf{NP}$-completeness of a meta-complexity problem in $\mathsf{NP}$ under randomized non-adaptive reductions in the unrelativized setting. The conclusion depends on the reduction running faster than the time bound $t$ of the Kolmogorov measure: if $K^{\mathrm{poly}}$ is $\mathsf{NP}$-complete under such reductions, the reductions likely need a lot of time.

## Expansion

Derandomizing the reduction directly fails, because the consistency test it must fool already takes non-deterministic time $t$. Instead, assuming $\mathsf{E}$ requires exponential-size non-deterministic circuits, a hitting set generator with optimal seed length shows that for samples $q$ from any distribution samplable in time $t'$, with high probability $K^t(q)$ and $K(q)$ differ by $O(\log|q|)$, with $t$ polynomial in $t'$. Then the reduction to $K^t$ is a reduction to approximating $K$, and the $\mathsf{AM}\cap\mathsf{coAM}$ upper bound applies; this works for unary languages, so every unary language in $\mathsf{NP}$ lands in $\mathsf{AM}\cap\mathsf{coAM}$, the derandomization hypothesis moves it to $\mathsf{NP}\cap\mathsf{coNP}$, and an upward translation gives $\mathsf{NE}=\mathsf{coNE}$.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Proof depends on

- [Randomized non-adaptive reductions to approximating Kolmogorov complexity](randomized-nonadaptive-reductions-to-approximating-kolmogorov-complexity.md)

## Sources

- Michael Saks and Rahul Santhanam, "On Randomized Reductions to the Random Strings", *37th Computational Complexity Conference (CCC 2022)*, LIPIcs, 2022, https://doi.org/10.4230/LIPIcs.CCC.2022.29 (Theorem 2, Theorem 6, Section 1.1.2, proof overview in Section 1.2).
