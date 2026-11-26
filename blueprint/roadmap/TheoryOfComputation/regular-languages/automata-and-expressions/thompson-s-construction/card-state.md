# Number of states of Thompson's automaton

For every regular expression $r$, the number of
states of Thompson's automaton of $r$ is $n(r)$, the Thompson state count of $r$: $n(0) = 0$,
$n(\varepsilon) = 1$, $n(a) = 2$ for a letter $a$, $n(P + Q) = n(P) + n(Q)$, $n(PQ) = n(P) + n(Q)$
and $n(P^*) = n(P) + 1$.
