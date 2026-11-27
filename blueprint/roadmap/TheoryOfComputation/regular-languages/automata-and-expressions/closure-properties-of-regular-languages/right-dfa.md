# DFA for the right quotient by a language

Given a DFA $M$ over an alphabet $T$ with state
set $\sigma$ and a language $R$ over $T$, this is the DFA with the same states, transition function
and start state as $M$, whose accepting states are the states $q$ from which some word of $R$
leads $M$ to an accepting state of $M$.

The accepting set is defined by quantifying over $R$, so it is not computable in general.
