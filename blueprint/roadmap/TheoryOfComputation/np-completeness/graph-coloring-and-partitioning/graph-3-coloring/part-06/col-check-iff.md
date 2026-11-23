# Acceptance condition of the 3-COLOR verifier

For all bit strings $x$ and $w$, the verifier
accepts $(x, w)$ iff there are a natural number $n$ and a list $E$ of pairs of natural numbers
such that $x$ is the encoding of the graph with $n$ vertices and edge list $E$, both entries of
every pair in $E$ are less than $n$, $w$ has at least $2n$ bits, the color code of every vertex
$i < n$ in $w$ is valid, and for every $(u, v) \in E$ with $u \ne v$ the color codes of $u$ and
$v$ in $w$ differ.
