# Conditional KT complexity and the Minimum Conditional KT Problem McKTP

Conditional KT complexity $\mathrm{KT}(x\mid y)$ is the least value of $|\Pi|+t$ over programs $\Pi$ that, with random access to $y$, print every bit of $x$ within time $t$; McKTP compares it with a threshold.

Fix a universal Turing machine $U$ with random access to a program $\Pi$ and an auxiliary string $y$. For $x,y\in\{0,1\}^*$,

$$
\mathrm{KT}(x\mid y)=\min\{|\Pi|+t : U^{\Pi,y}(i,1^{t})=x_i \text{ for all } 1\le i\le |x|\},
$$

and $\mathrm{KT}(x)=\mathrm{KT}(x\mid\lambda)$ for the empty string $\lambda$. (The original definition also requires $U^{\Pi,y}(|x|+1,1^{t})=\ast$; the results hold under either convention.) There is a constant $c>0$ with $\mathrm{KT}(x\mid y)\le |x|+c\log|x|$ for all $x,y$.

For $n\in\mathbb{N}$ and $m:\mathbb{N}\to\mathbb{N}$, **McK$^m$TP of dimension $n$** is the decision problem: given $x\in\{0,1\}^{n}$, $y\in\{0,1\}^{m(n)}$ and a threshold $0\le\theta\le n+c\log n$ in binary, decide whether there are a program $\Pi$ and a time bound $t$ with $U^{\Pi,y}(i,1^{t})=x_i$ for all $1\le i\le n$ and $|\Pi|+t\le\theta$. For polynomial-time computable $m$ it is in NP. The search version outputs a pair $(\Pi,t)$ minimizing $|\Pi|+t$.

For $\alpha:\mathbb{N}\to[0,1]$, a function $f$ on $\{0,1\}^{n}$ is **$\alpha$-hard on average** ($\alpha$-HoA) if every probabilistic polynomial-time heuristic $H$ satisfies $\Pr_{x\sim\{0,1\}^{n},r}[H(x;r)=f(x)]\le 1-\alpha(n)$ for all sufficiently large $n$; instances of McK$^m$TP are drawn uniformly.

## Expansion

Conditioning lets the auxiliary string $y$ carry a hidden structure, such as an encoded Set Cover instance, that a short program can exploit through oracle queries; this is what makes the conditional problem provably NP-complete while the unconditional MKTP is not known to be. Membership in NP holds because a witness $(\Pi,t)$ with $|\Pi|+t\le\theta\le n+c\log n$ has polynomial length and is checked by running $U$ for $t$ steps on each of the $n$ indices.

## Depends on

- [Parallel time-bounded Kolmogorov complexity and average-case hardness of KT](parallel-kolmogorov-complexity-and-kt-average-case-hardness.md)

## Proof depends on

None.

## Sources

- Eric Allender, Mahdi Cheraghchi, Dimitrios Myrisiotis, Harsha Tirumala and Ilya Volkovich, "One-Way Functions and a Conditional Variant of MKTP", *41st IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2021)*, LIPIcs, 2021, https://doi.org/10.4230/LIPIcs.FSTTCS.2021.7 (Section 2.3.2, Corollary 9, Definitions 10, 12 and 16, Lemma 11).
