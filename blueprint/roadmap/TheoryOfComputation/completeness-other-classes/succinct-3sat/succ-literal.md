# Literals of a succinctly described formula

Let $C$ be a list of gates encoded as
(kind, references) pairs and let $n$, $i$ and $j$ be natural numbers. Give $C$, as a circuit on
$n + 2$ inputs, the input consisting of the $n$ lowest bits of $i$ followed by the $2$ lowest
bits of $j$, each least significant bit first, and let $(o_0, \dots, o_{p-1})$ be its last
$n + 1$ outputs. Literal $j$ of clause $i$ is the pair $(v, s)$ with
$v = \sum_{k < \min(n, p)} [o_k]\, 2^k$, where $[o_k]$ is $1$ if $o_k$ is true and $0$
otherwise, and polarity $s = o_n$, read as false when $p \le n$.
