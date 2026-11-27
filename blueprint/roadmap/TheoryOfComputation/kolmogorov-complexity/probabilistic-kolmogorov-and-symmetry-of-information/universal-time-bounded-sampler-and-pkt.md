# The universal time-bounded sampler hits every x with probability about 2^{−pK^t(x|y)}

Define the **universal time-bounded sampler** $\mathrm{USamp}(1^n,1^t,y)$: pick $k$ uniformly from $\{0,1,\dots,c n\}$, a uniformly random program $p\in\{0,1\}^k$ and a uniformly random $w\in\{0,1\}^t$; run $U(p,y,w)$ for $t$ steps and output the first $n$ bits it prints (or a fixed default string). It runs in time $\mathrm{poly}(n,t)$. For all $n,t$, all $x\in\{0,1\}^n$ and all $y$:

$$
\mathrm{pK}^t(x\mid y)\le k\ \Longrightarrow\ \Pr\bigl[\mathrm{USamp}(1^n,1^t,y)=x\bigr]\ \ge\ \Omega\!\left(\frac{1}{n\cdot 2^{k}}\right).
$$

Conversely every string output by a $\mathrm{poly}(n,t)$-time samplable distribution with probability $\delta$ is output by $\mathrm{USamp}$ with probability $\delta\cdot 2^{-O(\log n)}$ after suitable padding of the time bound.

## Proof sketch

With probability $\Omega(1/n)$ the sampler guesses the right length $k$; with probability at least $2/3$ the string $w$ is good, i.e. some program of length $k$ prints $x$ from $(y,w)$ within $t$ steps; and given a good $w$ the uniformly random $p$ equals that program with probability $2^{-k}$. Multiplying gives the bound. The converse follows by letting $p$ encode the sampler's code plus its random seed.

## Depends on

- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)

## Sources

- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
