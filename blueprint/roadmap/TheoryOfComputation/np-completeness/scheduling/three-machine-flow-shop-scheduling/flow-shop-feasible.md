# Feasible flow-shop schedules

Let an instance consist of jobs $1, \dots, n$, where job $j$
is a list of natural numbers whose $k$-th entry $p_{j,k}$ is its processing time on machine $k$
(read as $0$ if the list has fewer than $k$ entries), and a deadline $D$. The instance is
feasible when there are natural numbers $s_{j,k}$, for each job $j$ and each $k \in \{1, 2, 3\}$,
such that for every job $j$ we have $s_{j,1} + p_{j,1} \le s_{j,2}$,
$s_{j,2} + p_{j,2} \le s_{j,3}$ and $s_{j,3} + p_{j,3} \le D$, and for every machine
$k \in \{1, 2, 3\}$ and all jobs $a < b$ we have $s_{a,k} + p_{a,k} \le s_{b,k}$ or
$s_{b,k} + p_{b,k} \le s_{a,k}$.

Each job visits machines 1, 2 and 3 in order and finishes by $D$. The pairwise condition also
applies to zero-duration operations. Such an operation may start at either endpoint of another
operation on the same machine, but cannot start strictly inside it. Treating zero-duration
operations as empty intervals would permit such a start.
