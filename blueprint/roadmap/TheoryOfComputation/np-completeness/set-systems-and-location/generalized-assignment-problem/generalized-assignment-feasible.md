# Feasible generalized assignments

Let $(R, C, c, K)$ be a generalized-assignment instance,
let $n$ be the number of rows of $R$ (the jobs) and $m$ the length of $c$ (the machines), and
read entries missing from $R$ or $C$ as $0$. The instance is feasible when there are machines
$a_1, \dots, a_n \in \{1, \dots, m\}$ such that for every machine $i$ the sum of $R_{j,i}$
over the jobs $j$ with $a_j = i$ is at most $c_i$, and $\sum_{j=1}^{n} C_{j,a_j} \le K$.
