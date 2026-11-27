# Saks–Zhou randomized rounding with a random shift

For $d \ge 0$, $x \in \mathbb{R}$ and a shift $y \in \{0, 1, \dots, 2^d - 1\}$, let $\mathrm{Snap}_d(x, y) = \max\bigl(2^{-d}\lfloor 2^d x - 2^{-d} y\rfloor, 0\bigr)$. Then $\mathrm{Snap}_d(x,y)$ is a nonnegative multiple of $2^{-d}$, and for $x \ge 0$ it lies in $[x - 2^{1-d}, x]$. If $|a - b| \le \varepsilon$, at most a $2^d\varepsilon + 2^{-d}$ fraction of the shifts $y$ give $\mathrm{Snap}_d(a, y) \ne \mathrm{Snap}_d(b, y)$. Applied entrywise to an $m \times m'$ matrix it maps substochastic matrices to substochastic matrices with entries in $2^{-d}\mathbb{N}$, and two matrices that are entrywise $\varepsilon$-close are rounded differently for at most an $mm'(2^d\varepsilon + 2^{-d})$ fraction of the shifts.

## Proof sketch

Count shifts exactly: for $a \le b$ the number of shifts with different integer parts is $\lfloor 2^{2d}b\rfloor - \lfloor 2^{2d}a\rfloor$, by Hermite's identity $\sum_{y<N}\lfloor z + y/N\rfloor = \lfloor Nz\rfloor$. The matrix version is a union bound over entries.

## Sources

- M. Saks and S. Zhou, "BP_H SPACE(S) ⊆ DSPACE(S^{3/2})", Journal of Computer and System Sciences 58(2), 376–403, 1999.
- E. Chattopadhyay and J.-J. Liao, "Optimal Error Pseudodistributions for Read-Once Branching Programs", 35th Computational Complexity Conference (CCC 2020), 2020.
