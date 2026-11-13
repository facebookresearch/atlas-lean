# Bounded reachability in a digraph

Let $E$ be a finite list of ordered pairs of natural
numbers, read as the arcs of a directed graph, and let $n$, $u$ and $v$ be natural numbers. Then
$v$ is reachable from $u$ within $n$ steps along $E$ when there are natural numbers
$w_0, w_1, \dots, w_k$ with $k \le n$, $w_0 = u$ and $w_k = v$ such that $(w_j, w_{j+1})$ occurs
in $E$ for every $j < k$.
