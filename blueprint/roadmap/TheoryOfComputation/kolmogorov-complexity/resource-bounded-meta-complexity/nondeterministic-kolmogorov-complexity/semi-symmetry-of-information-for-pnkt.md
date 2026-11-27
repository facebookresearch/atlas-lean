# Semi-symmetry and average-case symmetry of information for pnK^t

Probabilistic nondeterministic time-bounded complexity satisfies a worst-case semi-symmetry of information, with $\mathrm{pK}^t(x,y)$ on the left, and full symmetry of information on average over samplable pairs, unconditionally. Average-case symmetry of information fails for $\mathrm{pK}^t$ if one-way functions exist.

**Semi-symmetry.** There are polynomials $p_{SoI}$ and $p_0$ such that for all sufficiently large $x,y\in\{0,1\}^*$ and every $t\ge p_0(|x|+|y|)$,

$$
\mathrm{pK}^t(x,y)\ge\mathrm{pnK}^{p_{SoI}(t)}(y\mid x)+\mathrm{pnK}^{p_{SoI}(t)}(x)-\log p_{SoI}(t).
$$

**Average-case symmetry.** For every polynomial-time samplable family $\{D_n\}$ over $\{0,1\}^n\times\{0,1\}^n$ and every polynomial $q$ there is a polynomial $p$ such that for every computable $t\ge p(n)$ and all large $n$,

$$
\Pr_{(x,y)\sim D_n}\Bigl[\mathrm{pnK}^t(x,y)\ge\mathrm{pnK}^t(y\mid x)+\mathrm{pnK}^t(x)-c\log t\Bigr]\ge 1-\frac{1}{q(n)},
$$

where $c>0$ is a universal constant. Worst-case symmetry of information for $\mathrm{pnK}^t$ itself is open, and there is an oracle relative to which symmetry of information for $\mathrm{nK}^t$ fails.

## Expansion

For semi-symmetry the proof follows the direct-product-generator approach used to derive symmetry of information for $\mathrm{pK}^t$ from an easy MINKT: MINKT, which is in NP, serves as the distinguisher, and since the reconstruction makes only nonadaptive queries one gets $\mathrm{pK}^t(x,y)\ge\mathrm{pK}^{\mathrm{poly}(t),\parallel\mathrm{NP}}(y\mid x)+\mathrm{pK}^{\mathrm{poly}(t),\parallel\mathrm{NP}}(x)+O(\log t)$ with nonadaptive NP oracle access; a lemma converting nonadaptive NP-oracle complexity into $\mathrm{pnK}$ finishes. For the average-case statement, the coding theorem for $\mathrm{pK}^t$ bounds $\mathrm{pK}(x,y)$ by $\log(1/D_n(x,y))$ plus a logarithmic term, and with probability $1-1/q(n)$ this is at most $K(x,y)$ plus logarithmic terms, hence at most $\mathrm{pnK}^t(x,y)+c\log t$; combining with semi-symmetry gives the claim.

## Depends on

- [Probabilistic nondeterministic time-bounded complexity pnK^t](probabilistic-nondeterministic-complexity-pnkt.md)
- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](../../probabilistic-kolmogorov-and-symmetry-of-information/pkt-probabilistic-time-bounded-kolmogorov-complexity.md)
- [Polynomial-time symmetry of information hypothesis for K^t and pK^t](../../probabilistic-kolmogorov-and-symmetry-of-information/polynomial-time-symmetry-of-information-hypothesis.md)

## Proof depends on

- [Lu–Oliveira–Zimand: an optimal coding theorem for pK^t over polynomial-time samplable distributions](../../probabilistic-kolmogorov-and-symmetry-of-information/optimal-coding-theorem-for-pkt.md)

## Sources

- Jinqiao Hu, Zhenjian Lu and Igor C. Oliveira, "Hardness of Computing Nondeterministic Kolmogorov Complexity", *41st Computational Complexity Conference (CCC 2026)*, LIPIcs, 2026, [doi:10.4230/LIPIcs.CCC.2026.9](https://doi.org/10.4230/LIPIcs.CCC.2026.9) (Theorems 7 and 8 and their proofs in Section 3.4).
