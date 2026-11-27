# Distributional problems, DistNP, AvgP and HeurP

An **ensemble** is a family $\mathcal{D}=(D_n)_n$ of distributions with $D_n$ on $\{0,1\}^n$. It is **polynomial-time computable** ($\mathsf{PComp}$) if the cumulative distribution $x\mapsto\Pr_{D_n}[y\le x]$ (lexicographic order) is computable exactly in polynomial time, and **samplable** ($\mathsf{PSamp}$) if a probabilistic polynomial-time algorithm on $1^n$ outputs a sample of $D_n$. A distributional problem $(L,\mathcal{D})$ is in $\mathsf{DistNP}$ if $L\in\mathsf{NP}$ and $\mathcal{D}\in\mathsf{PComp}$. It is in $\mathsf{HeurP}$ if there is an algorithm $A(x,\delta)$ running in time polynomial in $n$ and $1/\delta$ and erring on a set of $D_n$-probability at most $\delta$ for every $n$ and $\delta$, and in $\mathsf{AvgP}$ if there is an errorless scheme that answers correctly or outputs 'don't know' with probability at most $\delta$.

## Depends on

- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [Samplable distributions](../impagliazzo-s-five-worlds/samplable.md)

## Sources

- Leonid A. Levin, "Average Case Complete Problems", SIAM Journal on Computing 15(1), 285–286, 1986.
- Andrej Bogdanov and Luca Trevisan, "Average-Case Complexity", Foundations and Trends in Theoretical Computer Science 2(1), 1–106, 2006, Definitions 1, 2, 6, 8 and 11 (there $D_n$ may live on $\{0,1\}^{\le m(n)}$; restricting to $\{0,1\}^n$ is the convention of Goldreich's textbook).
- Shai Ben-David, Benny Chor, Oded Goldreich and Michael Luby, "On the Theory of Average Case Complexity", Journal of Computer and System Sciences 44(2), 193–219, 1992.
