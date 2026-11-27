# Distributional reductions and domination

A **distributional reduction** from $(L,\mathcal{D})$ to $(L',\mathcal{D}')$ is a polynomial-time map $f$ with $x\in L\iff f(x)\in L'$ for all $x$ in the support of $\mathcal{D}$, together with a polynomially bounded length map $m(n)$, such that the image distribution is **dominated**: there is a polynomial $p$ with

$$
\Pr_{x\sim D_n}[f(x)=y]\le p(n)\cdot\Pr_{y'\sim D'_{m(n)}}[y'=y]\quad\text{for all }y.
$$

The classes $\mathsf{AvgP}$ and $\mathsf{HeurP}$ are closed under distributional reductions.

## Depends on

- [Distributional problems, DistNP, AvgP and HeurP](../distributional-problems.md)

## Sources

- Andrej Bogdanov and Luca Trevisan, "Average-Case Complexity", Foundations and Trends in Theoretical Computer Science 2(1), 1–106, 2006, Definition 17, Lemma 18 (the source requires domination only for $y$ in the support of $D'_{m(n)}$; requiring it for all $y$ is the slightly stronger form stated here).
- Leonid A. Levin, "Average Case Complete Problems", SIAM Journal on Computing 15(1), 1986.
