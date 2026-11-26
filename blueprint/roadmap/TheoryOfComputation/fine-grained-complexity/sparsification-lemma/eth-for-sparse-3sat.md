# ETH holds for sparse 3-SAT iff for general 3-SAT

If 3-SAT on instances with $n$ variables and $m = O(n)$ clauses can be solved in time $2^{o(n)}$ (equivalently $2^{o(m)}$), then 3-SAT on arbitrary instances can be solved in time $2^{o(n)}$. Hence the Exponential Time Hypothesis is equivalent to the statement that 3-SAT requires time $2^{\delta m}$ for some $\delta > 0$, where $m$ is the number of clauses, and it implies $2^{\Omega(n)}$ lower bounds for every problem to which 3-SAT reduces by linear-size reductions.

## Proof sketch

Sparsify with parameter $\varepsilon$: each of the $2^{\varepsilon n}$ sparse formulas has $O_\varepsilon(n)$ clauses and is solved in $2^{o(n)}$ time; letting $\varepsilon \to 0$ gives $2^{o(n)}$ overall.

## Depends on

- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)

## Proof depends on

- [Impagliazzo–Paturi–Zane sparsification lemma](impagliazzo-paturi-zane-sparsification-lemma.md)

## Sources

- R. Impagliazzo, R. Paturi and F. Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 512–530, 2001.
