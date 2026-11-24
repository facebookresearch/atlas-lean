# Total weighted completion time of a job order

Let $J$ be a list of jobs, each a pair
$(p_i, w_i)$ of processing time and weight indexed from $0$, with $(p_i, w_i) = (0, 0)$ for $i$
outside the list. For a list $j_1, \dots, j_m$ of job indices, the total weighted completion time
is $\sum_{k=1}^{m} w_{j_k} C_k$, where $C_k = p_{j_1} + \dots + p_{j_k}$ is the completion time of
the $k$-th job in the order.
