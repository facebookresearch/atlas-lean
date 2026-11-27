# Reductions to time-bounded random strings for fast-growing time bounds give P/poly

If a decidable set reduces in polynomial time, even adaptively, to the time-bounded random strings $R_{K^t}$ for a sufficiently fast-growing $t$, then answering only the logarithmically short queries correctly suffices, so the set is in P/poly. Hence the class $\mathrm{TTRT}$ lies between BPP and P/poly.

**Small circuits.** Suppose $A\in\mathrm{DTIME}(t_1)$ and $M : A\le^p_T R_{K^t}$ for time bounds $t,t_1$ with

$$
t(n+1)\ge 2^nt(n)+2^{2^n}t_1(2^n).
$$

If $M$ runs in time $n^c$ and $R'=R_{K^t}^{\le\lceil(c+1)\log n\rceil}$, then $M^{R'}(x)=A(x)$ for all $x\in\{0,1\}^n$; in particular $A\in\mathrm{P}/\mathrm{poly}$.

**The class $\mathrm{TTRT}$.** It consists of the languages $L$ for which there is a time bound $t_0$ such that $L\le^p_{tt}R_{K^t_U}$ for every time-efficient universal prefix machine $U$ and every time-constructible $t\ge t_0$. Every such $L$ is decidable, and

$$
\mathrm{BPP}\subseteq\mathrm{TTRT}\subseteq\mathrm{P}/\mathrm{poly}.
$$

**Contrast with $R_K$.** There is a truth-table reduction $M:\{0,1\}^*\le^p_{tt}R_K$ such that for all large $n$ and every $R'\subseteq\{0,1\}^{\le n-1}$ some $x\in\{0,1\}^n$ has $M^{R'}(x)\ne 1$; for $t(n+1)\gg 2^nt(n)$ this reduction behaves differently with oracles $R_K$ and $R_{K^t}$. Since $\mathrm{PSPACE}\le^p_T R_K$, the small-circuit theorem shows $\mathrm{PSPACE}\not\le^p_T R_{K^t}$ for large $t$ unless $\mathrm{PSPACE}\subseteq\mathrm{P}/\mathrm{poly}$.

## Expansion

If $M^{R'}$ erred on some length-$n$ input, the first such input could be found by brute force within time $2^{\ell}t(\ell)+2^{n+1}(t_1(n)+O(n^c))$ for $\ell=\lceil(c+1)\log n\rceil$, and every query $M$ makes on it would have a description of length $c\log n+O(1)$ running within that time. The error forces some long query of length $m>\ell$ to be $K^t$-random, but the growth condition makes the short description fast enough to show it is not, a contradiction. The inclusion $\mathrm{BPP}\subseteq\mathrm{TTRT}$ comes from Buhrman, Fortnow, Koucký and Loff with $t_0=2^{2^{2n}}$.

## Depends on

- [Sets of Kolmogorov-random strings R_C, R_K and R_{K^t}](kolmogorov-random-strings.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [Polynomial time with polynomial advice](../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [Polynomial space for decision problems](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

None.

## Sources

- Eric Allender, Harry Buhrman, Luke Friedman and Bruno Loff, "Reductions to the set of random strings: The resource-bounded case", *Logical Methods in Computer Science* 10(3:5), 2014, DOI 10.2168/LMCS-10(3:5)2014, [arXiv:1406.7658v2](https://arxiv.org/abs/1406.7658v2) (Definition 2.2, Theorem 2.3, Proposition 2.5, Theorem 3.2 and the corollary after it, Theorem 3.3, Section 3).
