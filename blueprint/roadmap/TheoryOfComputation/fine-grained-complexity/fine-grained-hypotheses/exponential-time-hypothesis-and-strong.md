# Exponential Time Hypothesis and Strong Exponential Time Hypothesis

For $k \ge 3$, the $k$-SAT problem asks whether a CNF formula whose clauses have at most $k$ literals has a satisfying assignment, and running times are measured in the number $n$ of variables.

- *Exponential Time Hypothesis* (ETH; Impagliazzo and Paturi): let $s_k$ be the infimum of the $\delta$ for which there is an $O(2^{\delta n})$-time algorithm for $k$-SAT. Then $s_k > 0$ for every $k \ge 3$; that is, $k$-SAT has no subexponential-time algorithm.
- *Strong Exponential Time Hypothesis* (SETH; Impagliazzo, Paturi and Zane): for every $\varepsilon > 0$ there is an integer $k \ge 3$ such that $k$-SAT on $n$ variables cannot be solved by a deterministic algorithm in time $O(2^{(1 - \varepsilon) n})$. The randomized variant, which also excludes randomized algorithms, is a separate and stronger hypothesis.

In fine-grained complexity both hypotheses are taken on the word-RAM with $O(\log n)$-bit words.

## Depends on

- [The word-RAM model](the-word-ram-model.md)

## Sources

- R. Impagliazzo and R. Paturi, "On the complexity of $k$-SAT", *Journal of Computer and System Sciences* 62(2):367–375, 2001; conference version *CCC 1999*, Section 1 (the definition of $s_k$ and of ETH)
- V. Vassilevska Williams, "On some fine-grained questions in algorithms and complexity", *Proceedings of the ICM 2018*, <http://people.csail.mit.edu/virgi/eccentri.pdf>, Section 2.1, Hypothesis 1
