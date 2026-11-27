# States of Thompson's automaton

The state set $S(r)$ of Thompson's automaton of a regular
expression $r$ is defined by structural recursion: $S(0)$ is empty, $S(\varepsilon)$ has one
element, $S(a)$ has two elements for a letter $a$, both $S(P + Q)$ and $S(PQ)$ are the disjoint
union $S(P) \sqcup S(Q)$, and $S(P^*)$ is $S(P)$ together with one new element.
