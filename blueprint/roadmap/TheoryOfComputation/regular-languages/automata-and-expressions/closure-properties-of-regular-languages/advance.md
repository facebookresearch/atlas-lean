# Next state while spelling out a letter's image

Let $M$ be a DFA over a finite alphabet $T$
with transition function $\delta$, and let $\varphi$ map each letter of $T$ to a word over $T'$. For
a state $q$ of $M$, a letter $a$ and a natural number $i$, the state reached after emitting position
$i$ (counted from $0$) of $\varphi(a)$ from $q$ is the intermediate state $(q, a, i + 1)$ of the
ε-NFA if $i + 1 < |\varphi(a)|$, and the state $\delta(q, a)$ of $M$ otherwise.
