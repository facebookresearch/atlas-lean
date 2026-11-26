# Average-case symmetry of information, conditional coding and language compression over samplable pairs

Let $\{D_n\}$ be a polynomial-time samplable family, each $D_n$ over $\{0,1\}^n\times\{0,1\}^n$, with conditional law $D_n(x\mid y)$. Say that, for $\{D_n\}$:

1. **average-case SoI for $\mathrm{pK}$** holds if for every polynomial $q$ there is a polynomial $p$ such that for every computable $t\ge p$ and all large $n$,
$\Pr_{(x,y)\sim D_n}\bigl[\mathrm{pK}^{t(n)}(x,y)\ge \mathrm{pK}^{t(n)}(x\mid y)+\mathrm{pK}^{t(n)}(y)-\log t(n)\bigr]\ge 1-1/q(n)$;
2. **average-case conditional coding** holds if for every polynomial $q$ there is a polynomial $p$ with
$\Pr_{(x,y)\sim D_n}\bigl[\mathrm{pK}^{p(n)}(x\mid y)\le \log\tfrac{1}{D_n(x\mid y)}+\log p(n)\bigr]\ge 1-1/q(n)$ for all large $n$;
3. **average-case language compression** holds if for every recursively enumerable $L\subseteq\bigcup_n\{0,1\}^n\times\{0,1\}^n$ and every polynomial $q$ there is a polynomial $p$ such that, with $L_y=\{x:(x,y)\in L\}$,
$\Pr_{(x,y)\sim D_n}\bigl[x\in L_y\Rightarrow \mathrm{pK}^{p(n)}(x\mid y)\le\log|L_y|+\log p(n)\bigr]\ge 1-1/q(n)$.

The **independent** variants sample $y\sim C_n$ from a second samplable family supported on the second marginal of $D_n$ and then $x\sim D_n(\cdot\mid y)$; the **worst-case** variants require the bound for every pair in the support. Note that the same time bound $t(n)$ appears on both sides of item 1.

## Depends on

- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)
- [Polynomial-time symmetry of information hypothesis for K^t and pK^t](polynomial-time-symmetry-of-information-hypothesis.md)

## Sources

- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
