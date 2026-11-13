# PATH ∈ P

**PATH ∈ P** (Sipser, Theorem 7.14). The decision problem PATH belongs to the class P of
decision problems decidable in polynomial time. Here PATH accepts a bit string exactly when it
encodes natural numbers $s$, $t$, $n$ and a list $E$ of pairs of natural numbers such that
$s < n$, $t < n$ and $t$ is reachable from $s$ in zero or more steps along the arcs of $E$ below
$n$, the pairs $(u, v) \in E$ with $u < n$ and $v < n$.
