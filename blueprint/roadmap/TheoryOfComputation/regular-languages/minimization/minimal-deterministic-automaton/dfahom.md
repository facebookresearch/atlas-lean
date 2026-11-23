# Morphisms of DFAs

Let $M$ and $N$ be DFAs over the same alphabet with transition
functions $\delta_M$ and $\delta_N$. A morphism from $M$ to $N$ is a map $f$ from the states of
$M$ to the states of $N$ that sends the start state of $M$ to the start state of $N$, satisfies
$f(\delta_M(q, a)) = \delta_N(f(q), a)$ for every state $q$ of $M$ and every symbol $a$, and
such that each state $q$ of $M$ is accepting if and only if $f(q)$ is accepting in $N$.
