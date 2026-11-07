# Parameterized Clique

The parameterized $k$-Clique problem answers a bitstring $x$ and
a parameter $k \in \mathbb{N}$ as follows. If $x$ decodes, under the canonical bitstring
encoding, to a pair $(n, E)$ of a natural number $n$ and a list $E$ of pairs of natural numbers,
the answer is true exactly when there is a list of $k$ distinct natural numbers, each less than
$n$, such that for any two distinct entries $u$ and $v$ of the list, $(u, v) \in E$ or
$(v, u) \in E$. If $x$ decodes to no such pair, the answer is false.

That is, on a well-formed input the answer says whether the graph on the vertices
$0, \dots, n - 1$ whose edges are the pairs in $E$, with direction ignored, has a clique of
size $k$.
