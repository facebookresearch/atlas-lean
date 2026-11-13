# The ε-NFA for a substitution

Let $M$ be a DFA over $T$ with states $\sigma$, and for each
letter $a \in T$ let $N_a$ be a DFA over $T'$ with states $\tau_a$. This ε-NFA over $T'$ has as
states the states $q$ of $M$ and the triples $(q, a, p)$ with $q$ a state of $M$, $a \in T$ and
$p$ a state of $N_a$, read as the state $p$ of the copy of $N_a$ entered from $q$. A state $q$ of
$M$ has an ε-move to $(q, a, s_a)$ for every $a \in T$, where $s_a$ is the start state of $N_a$,
and no letter moves. A state $(q, a, p)$ moves on a letter $b$ to $(q, a, \delta_a(p, b))$, where
$\delta_a$ is the transition function of $N_a$, and has an ε-move, to the state $\delta_M(q, a)$
of $M$, exactly when $p$ is an accepting state of $N_a$; here $\delta_M$ is the transition
function of $M$. The start state is the start state of $M$, and the accepting states are the
accepting states of $M$.
