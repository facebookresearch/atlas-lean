# Feasible GENERALIZED 0-1 ASSIGNMENT instances

A 0-1 matrix $X$ of the **declared** shape $m \times n$ (not necessarily the stored shape of $A$), with exactly one $1$ in each column, such that $\sum_j A_{r j} X_{r j} \le b_r$ for every row $r < m$ (entrywise products summed along the row, not a matrix product), and with total cost $\sum_i \sum_j C_{i j} X_{i j} \le K$. The coefficients are those of [entry-a](entry-a.md), [entry-b](entry-b.md) and [entry-c](entry-c.md): missing entries read as zero, so for $m = n = 1$ even $A = b = C = [\,]$ has defined zero coefficients.
