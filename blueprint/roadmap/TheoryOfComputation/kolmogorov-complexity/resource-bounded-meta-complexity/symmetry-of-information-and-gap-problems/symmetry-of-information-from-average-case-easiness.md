# DistNP ⊆ AvgP implies symmetry of information for K^t

If NP is easy on average, time-bounded Kolmogorov complexity satisfies symmetry of information: $K^{p(t)}(x\mid y)+K^{p(t)}(y)-\log p(t)\le K^t(x,y)$. This improves the thirty-year-old result of Longpré and Watanabe, which assumed P = NP, and is proved meta-computationally from an algorithm approximating $K^t$.

**Symmetry of information (SoI)** is the hypothesis that there is a polynomial $p$ such that for all strings $x,y$ and every $t\ge|x|+|y|$,

$$
K^{p(t)}(x\mid y)+K^{p(t)}(y)-\log p(t)\le K^t(x,y).
$$

**Theorem.** If $\mathrm{DistNP}\subseteq\mathrm{AvgP}$, in the errorless sense (every NP language has an errorless heuristic scheme under every polynomial-time samplable distribution), then SoI holds. More precisely, if $\mathrm{GapMINKT}\in\mathrm{P}$ and $\mathrm{E}\not\subseteq\mathrm{i.o.SIZE}(2^{\varepsilon n})$ for some $\varepsilon>0$, then SoI holds.

**Sandwich.** Assume $\mathrm{E}\not\subseteq\mathrm{i.o.SIZE}(2^{\varepsilon n})$ for some $\varepsilon>0$. Consider: (1) $\mathrm{GapMINKT}\in\mathrm{P}$; (2) for every polynomial-time samplable $D$ and all sufficiently large polynomials $t$, an errorless heuristic scheme computes $K^{t(n)}(x)$ for $x\sim D_n$; (3) SoI holds; (4) the same with an error-prone heuristic scheme; (5) $\mathrm{Gap}_\tau\mathrm{MINKT}\in\mathrm{DTIME}(2^{O(n/\log n)})$ for some $\tau(n,t)=2^{O(n/\log n)}$. Then $1\iff 2\Rightarrow 3\Rightarrow 4$ and $3\Rightarrow 5$ (formal version in Theorem 8.2).

## Expansion

Both hypotheses of the precise form follow from $\mathrm{DistNP}\subseteq\mathrm{AvgP}$ (Buhrman, Fortnow and Pavan give the circuit lower bound; Hirahara's reductions give $\mathrm{GapMINKT}\in\mathrm{P}$, item 1 of the $\mathrm{Gap}(K^A\text{ vs }K)$ theorem with $A=\varnothing$). The proof compares the approximate complexities of $(\mathrm{DP}_k(x;z),\mathrm{DP}_\ell(y;z'))$, $(w,\mathrm{DP}_\ell(y;z'))$ and $(w,w')$, where $\mathrm{DP}_k(x;z)=(z^1,\dots,z^k,\langle z^1,x\rangle,\dots,\langle z^k,x\rangle)$ is the $k$-wise direct product generator. Random pairs are incompressible; the deterministic reconstruction property makes $\mathrm{DP}_\ell(y;\cdot)$ pseudorandom against the efficient approximation algorithm when $\ell\ll K^{p(t)}(y)$, and similarly for $x$ given $y$; reading off the gaps measured by the algorithm yields the inequality.

## Depends on

- [The promise problem GapMINKT](gap-minkt-promise-problem.md)
- [Polynomial-time symmetry of information hypothesis for K^t and pK^t](../../probabilistic-kolmogorov-and-symmetry-of-information/polynomial-time-symmetry-of-information-hypothesis.md)
- [Errorless average-case easiness: DistNP ⊆ AvgP, AvgBPP and Heuristica](errorless-average-case-easiness.md)

## Proof depends on

- [Few strings have small complexity](../../incompressible-strings-and-kolmogorov-complexity/card-lt-two-pow.md)
- [Gap(K^A vs K) is easy if NP^A is easy on average](gap-k-oracle-versus-k-under-average-case-easiness.md)

## Sources

- Shuichi Hirahara, "Symmetry of Information from Meta-Complexity", *37th Computational Complexity Conference (CCC 2022)*, LIPIcs 234, 2022, [doi:10.4230/LIPIcs.CCC.2022.26](https://doi.org/10.4230/LIPIcs.CCC.2022.26) (Definition 1.1, Theorems 1.2 and 1.3, Lemma 2.2, Theorem 4.1, Theorem 8.2).
