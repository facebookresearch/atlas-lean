# Encoding of a PATH instance

Writing $1$ for true and $0$ for false, the instance with
source $s$, target $t$ and the digraph given by $n$ and the edge list $E$ is encoded as $s$ ones,
a zero, $t$ ones, a zero, then $n$ ones and a zero, followed, for each pair $(u, v)$ of $E$ in
order, by $u$ ones, a zero, $v$ ones and a zero.
