# The ε-NFA for the homomorphic image

Let $M$ be a DFA over a finite alphabet $T$ with start
state $q_0$, transition function $\delta$ and accepting states $F$, let $\varphi$ map letters of $T$
to words over $T'$, and let $N$ be the maximum of the lengths $|\varphi(a)|$ over $a \in T$. The
ε-NFA over $T'$ has as states the states of $M$ together with the triples $(q, a, i)$ with $q$ a
state of $M$, $a \in T$ and $0 \le i < N$. Write $\mathrm{next}(q, a, i)$ for $(q, a, i + 1)$ if
$i + 1 < |\varphi(a)|$ and for $\delta(q, a)$ otherwise. From a state $q$ of $M$, reading $b$ leads
to $\mathrm{next}(q, a, 0)$ for each letter $a$ whose image starts with $b$, and an ε-move leads to
$\delta(q, a)$ for each letter $a$ with $\varphi(a)$ empty. From $(q, a, i)$, reading $b$ leads to
$\mathrm{next}(q, a, i)$ if the letter of $\varphi(a)$ at position $i$ (counted from $0$) is $b$,
and there are no ε-moves. The only start state is $q_0$ and the accepting states are those in
$F$.
