# NP-hardness of approximating conditional K^t would exclude Heuristica

If approximating time-bounded conditional Kolmogorov complexity $K^t(x\mid y)$, up to a computational-depth term and a logarithmic additive error, is NP-hard under randomized reductions, then Heuristica does not exist: NP is easy on average only if P = NP. Symmetry of information is the bridge from conditional to unconditional complexity.

The $(s,t)$-time-bounded computational depth is $\mathrm{cd}^{s,t}(x)=K^s(x)-K^t(x)$. SoI is the symmetry-of-information hypothesis $K^{p(t)}(x\mid y)+K^{p(t)}(y)-\log p(t)\le K^t(x,y)$ for a polynomial $p$, all $x,y$ and all $t\ge|x|+|y|$. Throughout, $\mathrm{DistNP}\subseteq\mathrm{AvgP}$ is meant in the errorless sense, and Heuristica is Hirahara's: $\mathrm{P}\ne\mathrm{NP}$ and $\mathrm{DistNP}\subseteq\mathrm{AvgP}$. For a polynomial $\tau:\mathbb{N}^3\to\mathbb{N}$, $\mathrm{Gap}_\tau\mathrm{MINcKT}$ is the promise problem with

$$
\Pi_{\mathrm{Yes}}=\{(x,y,1^t,1^s) : K^t(x\mid y)\le s-\mathrm{cd}^{t,\tau(|x|,|y|,t)}(y)\},\qquad
\Pi_{\mathrm{No}}=\{(x,y,1^t,1^s) : K^{\tau(|x|,|y|,t)}(x\mid y)>s+\log\tau(|x|,|y|,t)\}.
$$

1. If SoI holds and $\mathrm{GapMINKT}\in\mathrm{P}$, then $\mathrm{Gap}_\tau\mathrm{MINcKT}\in\mathrm{P}$ for some polynomial $\tau$.
2. If $\mathrm{DistNP}\subseteq\mathrm{AvgP}$, then $\mathrm{Gap}_\tau\mathrm{MINcKT}\in\mathrm{P}$ for some polynomial $\tau$.
3. If $\mathrm{Gap}_\tau\mathrm{MINcKT}$ is NP-hard under randomized reductions for every polynomial $\tau$, then Heuristica does not exist: $\mathrm{DistNP}\subseteq\mathrm{AvgP}$ if and only if $\mathrm{P}=\mathrm{NP}$.

Complementing item 3, Hirahara proves NP-hardness of $\mathrm{Gap}_\tau\mathrm{MINcKT}$ when $\tau$ is sublinear in $|y|$, for example $\tau(|x|,|y|,t)\le|x|^{O(1)}|y|^{0.99}t^{O(1)}$ (Theorem 1.6, formal version Theorem 6.6).

## Expansion

Under SoI, $K^t(x\mid y)$ is approximated by $K(x,y)-K(y)$ with polynomially related time bounds; the depth term absorbs the gap between the time bounds used for $y$. An algorithm approximating unconditional $K^t$ therefore approximates the conditional version, giving item 1, and item 2 follows by combining it with the theorem that average-case easiness of NP implies SoI and with $\mathrm{GapMINKT}\in\mathrm{P}$, which is item 1 of the $\mathrm{Gap}(K^A\text{ vs }K)$ theorem with $A=\varnothing$. For item 3, if NP is easy on average then $\mathrm{Gap}_\tau\mathrm{MINcKT}$ is in P for some $\tau$, and NP-hardness of it under randomized reductions gives $\mathrm{NP}\subseteq\mathrm{BPP}$; average-case easiness of NP also yields the exponential circuit lower bound for E that derandomizes BPP, so $\mathrm{P}=\mathrm{NP}$. The converse direction is immediate.

## Depends on

- [The promise problem GapMINKT](gap-minkt-promise-problem.md)
- [Errorless average-case easiness: DistNP ⊆ AvgP, AvgBPP and Heuristica](errorless-average-case-easiness.md)
- [Computational depth](../../time-bounded-kolmogorov-complexity/computational-depth.md)
- [Polynomial-time symmetry of information hypothesis for K^t and pK^t](../../probabilistic-kolmogorov-and-symmetry-of-information/polynomial-time-symmetry-of-information-hypothesis.md)

## Proof depends on

- [DistNP ⊆ AvgP implies symmetry of information for K^t](symmetry-of-information-from-average-case-easiness.md)
- [Gap(K^A vs K) is easy if NP^A is easy on average](gap-k-oracle-versus-k-under-average-case-easiness.md)

## Sources

- Shuichi Hirahara, "Symmetry of Information from Meta-Complexity", *37th Computational Complexity Conference (CCC 2022)*, LIPIcs 234, 2022, [doi:10.4230/LIPIcs.CCC.2022.26](https://doi.org/10.4230/LIPIcs.CCC.2022.26) (Theorem 1.5, Definitions 3.5 and 6.1, Proposition 6.2, Corollary 6.3, Theorem 6.6).
