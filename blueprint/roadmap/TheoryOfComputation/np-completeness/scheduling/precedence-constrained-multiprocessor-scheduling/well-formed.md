# Well-formed precedence-multiprocessor scheduling instances

An instance $(d, P, m, D)$
whose list of job durations $d$ has length $n$ is well formed when every precedence pair
$(a, b) \in P$ satisfies $a < n$, $b < n$ and $a \ne b$, and there is an ordering of the jobs
$0, \dots, n-1$ (a permutation of this list) in which $a$ comes before $b$ for every
$(a, b) \in P$.
