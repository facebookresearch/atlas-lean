# One step of a composite transducer: the output

Let $S_1$ be a sequential transducer from
$I$ to $M$, $S_2$ one from $M$ to $O$, and $C$ their composition. Let $q_1$ be a state of $S_1$,
$q_2$ a state of $S_2$ and $a \in I$ a letter, and let $w$ be the word $S_1$ emits when it reads
$a$ in state $q_1$. Then the word $C$ emits when it reads $a$ in state $(q_1, q_2)$ is the
concatenation of the words $S_2$ emits while reading $w$ from $q_2$.
