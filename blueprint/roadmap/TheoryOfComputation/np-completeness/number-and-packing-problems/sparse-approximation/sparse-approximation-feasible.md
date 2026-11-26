# Feasible instances of SPARSE APPROXIMATION

An instance $(n, A, b, \varepsilon, k)$ of SPARSE APPROXIMATION is feasible when some real vector $x = (x_0, \dots, x_{n-1})$ with at most $k$ nonzero entries satisfies

$$
\sqrt{\sum_{r < m} \Bigl( \sum_{c < n} A_{rc} \, x_c - b_r \Bigr)^2} \le \varepsilon,
$$

where $m$ is the length of $b$, $n$ is the declared number of columns, and $A_{rc}$, $b_r$ and $\varepsilon$ are the values of the [matrix entries](entry.md), the [right-hand side entries](rhs.md) and the code $\varepsilon$. The formula applies without well-formedness: only the first $m$ stored rows of $A$ and the first $n$ entries of each take part, missing entries count as $0$, a code with denominator $0$ counts as $0$, and the bound $\varepsilon$ may be zero or negative. For example, when $b$ is empty the left side is $0$ whatever the stored rows, so the instance is feasible exactly when $\varepsilon \ge 0$. Feasibility does not include well-formedness; the decision problem requires both. For a [well-formed](well-formed.md) instance this is the usual condition $\lVert A x - b \rVert_2 \le \varepsilon$ for $A \in \mathbb{Q}^{m \times n}$ and $b \in \mathbb{Q}^m$.
