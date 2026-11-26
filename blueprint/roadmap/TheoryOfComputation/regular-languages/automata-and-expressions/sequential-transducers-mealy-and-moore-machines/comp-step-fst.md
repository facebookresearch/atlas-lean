# One step of a composite transducer: the successor state

Let $S_1$ be a sequential
transducer from $I$ to $M$, $S_2$ one from $M$ to $O$, and $C$ their composition. Let $q_1$ be a
state of $S_1$, $q_2$ a state of $S_2$ and $a \in I$ a letter, and suppose that $S_1$, reading
$a$ in state $q_1$, moves to $q_1'$ and emits the word $w$. Then $C$, reading $a$ in state
$(q_1, q_2)$, moves to $(q_1', q_2')$, where $q_2'$ is the state $S_2$ reaches by reading $w$
from $q_2$.
