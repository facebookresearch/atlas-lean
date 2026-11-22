# Thompson state count

The state count $n(r)$ of a regular expression $r$ is defined by
structural recursion: $n(0) = 0$, $n(\varepsilon) = 1$, $n(a) = 2$ for a letter $a$,
$n(P + Q) = n(P) + n(Q)$, $n(PQ) = n(P) + n(Q)$ and $n(P^*) = n(P) + 1$.

It is the number of states of Thompson's automaton of $r$.
