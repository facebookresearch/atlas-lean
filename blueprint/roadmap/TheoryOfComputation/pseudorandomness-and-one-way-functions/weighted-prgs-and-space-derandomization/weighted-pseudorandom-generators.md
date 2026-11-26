# Weighted pseudorandom generators (pseudorandom pseudodistributions)

Recall that a standard-order read-once branching program (ROBP) of width $w$ and length $n$ has layers $V_0,\dots,V_n$ of $w$ vertices each, a start vertex in $V_0$, a set of accept vertices in $V_n$, and for each $i$ two edges labeled $0,1$ from every vertex of $V_{i-1}$ into $V_i$; on $x\in\{0,1\}^n$ it follows the edges labeled $x_1,\dots,x_n$ and accepts iff it ends in an accept vertex. Space-$S$ randomized algorithms that halt on every sequence of coin tosses, viewed as functions of their random bits, are ROBPs of width and length $2^{O(S)}$: no nonhalting cycle of configurations is reachable, so they run for at most $2^{O(S)}$ steps. Halting with probability one does not suffice, since a machine may toss coins until heads and so have arbitrarily long branches.

Let $\mathcal{F}$ be a class of functions $f:\{0,1\}^n\to\{0,1\}$. An **$\varepsilon$-weighted pseudorandom generator** (WPRG, also called a pseudorandom pseudodistribution generator) for $\mathcal{F}$ with seed length $r$ is a pair $(G,\rho)$ with $G:\{0,1\}^r\to\{0,1\}^n$ and $\rho:\{0,1\}^r\to\mathbb{R}$ such that for every $f\in\mathcal{F}$,

$$
\Bigl|\ \mathbb{E}_{y\in\{0,1\}^r}\bigl[\rho(y)\,f(G(y))\bigr]-\mathbb{E}_{x\in\{0,1\}^n}\bigl[f(x)\bigr]\ \Bigr|\le\varepsilon.
$$

An ordinary PRG is the case $\rho\equiv 1$. The WPRG is explicit if $G(y)$ and $\rho(y)$ are computable in space $O(r)$, with $|\rho(y)|\le 2^{O(r)}$. An explicit WPRG for width-$n$ length-$n$ ROBPs with seed length $O(\log n)$ and constant error would imply $\mathsf{BPL}=\mathsf{L}$, by computing the weighted average over all seeds. Negative weights allow cancellations that probability distributions cannot achieve; an explicit WPRG with nonnegative weights converts into an explicit PRG with comparable parameters.

## Depends on

- [Pseudorandom generators with logarithmic seed derandomize BPP](../derandomization/pseudorandom-generators-with-logarithmic-seed.md)

## Sources

- Mark Braverman, Gil Cohen and Sumegha Garg, "Pseudorandom Pseudo-distributions with Near-Optimal Error for Read-Once Branching Programs", STOC (2018); SIAM Journal on Computing 49(5) (2020), ECCC TR17-161.
- Edward Pyne and Salil Vadhan, "Pseudodistributions That Beat All Pseudorandom Generators", CCC (2021); Theory of Computing 22(3) (2026), ECCC TR21-019.
- William M. Hoza, "Better Pseudodistributions and Derandomization for Space-Bounded Computation", APPROX/RANDOM (2021), ECCC TR21-048.
