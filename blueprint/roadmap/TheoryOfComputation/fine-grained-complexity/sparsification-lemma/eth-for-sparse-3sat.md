# ETH holds for sparse 3-SAT iff for general 3-SAT

3-SAT on $n$ variables and $m$ clauses is solvable in time $2^{\delta n}\mathrm{poly}(n+m)$ for every $\delta>0$ if and only if it is solvable in time $2^{\delta m}\mathrm{poly}(n+m)$ for every $\delta>0$. Hence the Exponential Time Hypothesis is equivalent to the statement that for some $\delta > 0$ no algorithm solves 3-SAT in time $2^{\delta m}\mathrm{poly}(n+m)$, and also to the statement that for some $\delta>0$ none solves it in time $2^{\delta(n+m)}\mathrm{poly}(n+m)$; consequently, under ETH, no problem to which 3-SAT reduces in polynomial time with output size $O(n+m)$ is solvable in time $2^{o(\text{size})}$.

## Proof sketch

One direction is trivial, since variables occurring in no clause can be deleted, leaving $n\le 3m$. Conversely, given $\delta>0$, sparsify with $\varepsilon=\delta/2$: each of the at most $2^{\delta n/2}$ formulas has at most $K(\delta)n$ clauses and is solved in time $2^{\delta' K(\delta) n}$ with $\delta'=\delta/(2K(\delta))$, for a total of $2^{\delta n}\mathrm{poly}$.

## Depends on

- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)

## Proof depends on

- [Impagliazzo–Paturi–Zane sparsification lemma](impagliazzo-paturi-zane-sparsification-lemma.md)

## Sources

- R. Impagliazzo, R. Paturi and F. Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 512–530, 2001, Corollary 1.
- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015, Theorems 14.3 and 14.4.
