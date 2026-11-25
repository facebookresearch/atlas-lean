# Well-formed weighted radius-at-least instances

An instance $(n, E, C, K)$ is well formed when

- the list $E$ has no repeated entries, and every pair $(a, b)$ in $E$ satisfies $a < n$, $b < n$, $a \ne b$, and $(b, a) \notin E$;
- the graph of the instance is a tree (connected and acyclic, so in particular $n \ge 1$);
- $C$ has as many entries as $E$;
- $K > 0$.
