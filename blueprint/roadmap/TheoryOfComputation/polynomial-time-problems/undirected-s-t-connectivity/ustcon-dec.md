# Undirected s-t connectivity as a decision problem

A bitstring $x$ is a yes-instance
exactly when bitstring decoding of $x$, as a tuple $(n, E, s, t)$ of natural numbers $n$, $s$, $t$
and a finite list $E$ of pairs of natural numbers, succeeds and returns $(n, E, s, t)$ such that
$s < n$, $t < n$, and there are pairwise distinct natural numbers $v_0, \dots, v_k$, all less than
$n$, with $v_0 = s$, $v_k = t$ and, for every $i < k$, $(v_i, v_{i+1}) \in E$ or
$(v_{i+1}, v_i) \in E$.
