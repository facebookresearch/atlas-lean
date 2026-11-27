# Minimized DFA

Let $M$ be a DFA accepting the language $L$. The minimized DFA of $M$
has as states the reachable residuals of $M$, that is, the languages accepted by $M$ from the
states it reaches from its start state. Its start state is $L$; on a letter $a$ it moves from
a state $K$ to the left quotient $\{z : az \in K\}$; and its accepting states are those that
contain the empty word.

It is the canonical automaton of $L$, whose states are the left quotients of $L$, with each
state renamed to the same language viewed as a reachable residual of $M$.
