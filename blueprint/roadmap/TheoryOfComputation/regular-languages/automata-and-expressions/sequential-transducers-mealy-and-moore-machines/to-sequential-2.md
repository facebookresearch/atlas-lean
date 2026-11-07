# The sequential transducer of a Moore machine

Let $M$ be a Moore machine with transition
function $\delta$, output function $\lambda$ and start state $q_0$. Its sequential transducer has
the same states and the start state $q_0$; reading a letter $a$ in state $q$ it moves to
$\delta(q, a)$ and emits the one-letter word $\lambda(\delta(q, a))$; every state is accepting;
the initial output is the one-letter word $\lambda(q_0)$; and every final output is empty.
