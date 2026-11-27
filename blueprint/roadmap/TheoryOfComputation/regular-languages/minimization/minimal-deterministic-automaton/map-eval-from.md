# DFA morphisms commute with evaluation from a state

If $f$ is a morphism from a DFA $M$
to a DFA $N$, then for every state $q$ of $M$ and every word $x$, running $N$ on $x$ from $f(q)$
ends in the image under $f$ of the state reached by running $M$ on $x$ from $q$.
