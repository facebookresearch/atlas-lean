# Arc check of a vertex list

Given $n \in \mathbb{N}$ and a list $E$ of pairs of natural
numbers, the arc check of a list $p$ of natural numbers returns true when every two consecutive
entries $u, v$ of $p$ satisfy $(u, v) \in E$, $u < n$ and $v < n$, and false otherwise; in
particular every list with fewer than two entries passes.
