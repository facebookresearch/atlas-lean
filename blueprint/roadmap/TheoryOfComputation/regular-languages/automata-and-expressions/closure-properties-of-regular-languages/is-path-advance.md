# Finishing a letter's image in the image ε-NFA

Let $M$ be a DFA over a finite alphabet $T$
with transition function $\delta$, and let $\varphi$ map letters of $T$ to words over $T'$. For
every state $q$ of $M$, letter $a$ and natural number $i$, the ε-NFA of $M$ and $\varphi$ has a path
to the state $\delta(q, a)$ of $M$ from the state $(q, a, i + 1)$ if $i + 1 < |\varphi(a)|$, and
from $\delta(q, a)$ otherwise, whose labels are the letters of $\varphi(a)$ after position $i$
(positions counted from $0$), in order and all non-ε.
