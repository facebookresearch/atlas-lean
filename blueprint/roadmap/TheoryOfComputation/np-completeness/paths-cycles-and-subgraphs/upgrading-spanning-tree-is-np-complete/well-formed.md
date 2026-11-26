# Well-formed UPGRADING SPANNING TREE instances

An instance $(n, E, c, D, K)$ of UPGRADING SPANNING TREE is well formed when all of the following hold:

- the endpoint pairs $(u, v)$ of the entries of $E$ are pairwise distinct;
- every entry $(u, v, d_0, d_1, d_2)$ of $E$ has $u < n$, $v < n$ and $u \ne v$, and the reversed pair $(v, u)$ is not the endpoint pair of any entry of $E$;
- the graph of $E$ on $n$ vertices is connected;
- every entry of $E$ satisfies $d_0 \ge d_1 \ge d_2$;
- the cost list $c$ has exactly $n$ entries;
- $K > 0$.
