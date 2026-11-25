# NFA for the left quotient by a language

Given a DFA $M$ over an alphabet $T$ with state
set $\sigma$ and a language $R$ over $T$, this is the NFA with state set $\sigma$ and the same
accepting states as $M$, in which from a state $q$ on a letter $a$ the only possible move is to
the state $M$ reaches from $q$ on $a$, and whose start states are the states that $M$ reaches from
its start state on the words of $R$.

The set of start states is defined by quantifying over $R$, so it is not computable in general.
