# Well-formed longest-path instances

A longest-path instance $(n, E, K, s, t)$ is well
formed when $s < n$, $t < n$, the list $E$ has no repeated entries, and every pair $(u, v)$ in
$E$ satisfies $u < n$, $v < n$ and $u \ne v$, and its reverse $(v, u)$ does not belong to $E$.
