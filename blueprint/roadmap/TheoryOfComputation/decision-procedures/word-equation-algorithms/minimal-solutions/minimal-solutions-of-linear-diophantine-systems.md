# Size of minimal natural solutions of linear Diophantine systems

Every componentwise-minimal positive solution of a system of linear Diophantine equations has all entries at most $(w + r)\, e^{c/e}$, where $r$ is the number of unknowns, $w$ is $r$ plus the sum of the absolute values of the right-hand sides, and $c$ is the sum of the absolute values of the coefficients.

Consider a system of $m$ linear equations in $r \ge 1$ unknowns $x_1, \dots, x_r$ together with positivity constraints,

$$
\sum_{j=1}^{r} n_{i,j}\, x_j = n_i \quad (1 \le i \le m), \qquad x_j \ge 1 \quad (1 \le j \le r),
$$

with integers $n_{i,j}, n_i$, and consider its solutions in natural numbers, ordered componentwise: $(q_1, \dots, q_r) \ge (q'_1, \dots, q'_r)$ when $q_j \ge q'_j$ for all $j$. A solution is minimal if no other solution is strictly smaller in this order. Let

$$
w = r + \sum_{i=1}^{m} |n_i| \quad \text{and} \quad c = \sum_{i=1}^{m} \sum_{j=1}^{r} |n_{i,j}| .
$$

If $(q_1, \dots, q_r)$ is a minimal solution, then $q_j \le (w + r)\, e^{c/e}$ for every $j$.

## Depends on

None.

## Proof depends on

- [Hadamard's determinant inequality](../../../../LinearAlgebra/positive-definite-matrices/hadamard-s-inequality-and-determinant-bounds-for/hadamard-s-determinant-inequality/hadamard-determinant-inequality.md)

## Expansion

By a theorem of J. von zur Gathen and M. Sieveking and, independently, of J. L. Lambert, every minimal natural solution of $Ax = B$, $Cx \ge D$ has entries at most $(w + r) M$, where $M$ bounds the absolute values of the subdeterminants of the matrix formed by $A$ and $C$ (including the empty subdeterminant $1$) and $w$ is the sum of the absolute values of the entries of $B$ and $D$. Here $C$ is the identity, so it suffices to show $|\det N| \le e^{c/e}$ for every $k \times k$ submatrix $N$ of $(n_{i,j})$. For $k = 0$ the determinant is $1 = e^0 \le e^{c/e}$. For $k \ge 1$, Hadamard's inequality applied to the transpose of $N$, viewed as a complex matrix, bounds $|\det N|$ by the product of the Euclidean lengths of the columns of $N$, hence by $\prod_j s_j$ with $s_j = \sum_i |n_{i,j}|$ (over the rows of $N$). By the inequality between arithmetic and geometric means, $\prod_j s_j \le (c'/k)^k$ with $c' = \sum_j s_j \le c$. Finally $(x/k)^k \le e^{x/e}$ for $x \ge 0$: it is trivial for $x = 0$, and for $x > 0$ it is $k \ln y \le k y / e$ with $y = x/k$, which holds because $\ln y \le y / e$ for $y > 0$. This is the estimate of A. Kościelski and L. Pacholski (Journal of the ACM 43 (1996), Corollary 4.4), extended to the positivity constraints.

This page becomes ready once the bound of von zur Gathen–Sieveking and Lambert on minimal solutions (Jeż, Claim 5) is a page of its own.

## Sources

- Artur Jeż, "Recompression: a simple and powerful technique for word equations", arXiv:1203.3705v3 (2014), https://arxiv.org/abs/1203.3705v3; published in Journal of the ACM 63(1), Article 4 (2016), https://doi.org/10.1145/2743014; conference version STACS 2013, LIPIcs 20, 233–244, https://doi.org/10.4230/LIPIcs.STACS.2013.233, Lemma 36 and its proof (Section 8, "Minimal solutions of linear Diophantine systems"), including Claim 5
