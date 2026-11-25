# Fine-grained reductions

Let $A$ and $B$ be computational problems with conjectured running-time lower bounds $a(n)$ and $b(n)$. Then $A$ *$(a, b)$-reduces* to $B$, written $A \le_{a,b} B$, if for every $\varepsilon > 0$ there are $\delta > 0$ and an algorithm $R$ for $A$ that runs in time $a(n)^{1-\delta}$ on inputs of length $n$ and makes $q$ calls to an oracle for $B$ with query lengths $n_1, \dots, n_q$ such that

$$\sum_{i=1}^{q} b(n_i)^{1-\varepsilon} \le a(n)^{1-\delta}.$$


If $A \le_{a,b} B$ and $B \le_{b,a} A$, then $A$ and $B$ are *fine-grained equivalent*, written $A \equiv_{a,b} B$. These are Turing-style reductions: the reduction may make many adaptive oracle calls, as a single call to a decision problem does not in general solve a search problem.

## Depends on

- [The word-RAM model](the-word-ram-model.md)

## Sources

- V. Vassilevska Williams, "On some fine-grained questions in algorithms and complexity", *Proceedings of the ICM 2018*, <http://people.csail.mit.edu/virgi/eccentri.pdf>, Section 2.2, Definition 2.1
