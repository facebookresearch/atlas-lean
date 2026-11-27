# Spelling out a letter's image in the image ε-NFA

Let $M$ be a DFA over a finite alphabet
$T$ with transition function $\delta$, and let $\varphi$ map letters of $T$ to words over $T'$. For
every state $q$ of $M$ and letter $a$, the ε-NFA of $M$ and $\varphi$ has a path from the state $q$
to the state $\delta(q, a)$ whose label sequence is a single ε-label if $\varphi(a)$ is empty, and
the letters of $\varphi(a)$ in order, all non-ε, otherwise.
