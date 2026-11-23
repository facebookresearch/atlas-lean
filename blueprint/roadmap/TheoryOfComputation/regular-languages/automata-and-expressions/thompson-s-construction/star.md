# Kleene star of an ε-NFA

Given an ε-NFA $M$ with state set $\sigma$, its star automaton has
the states of $M$ together with one new state $q_0$, which is its only start state and its only
accepting state. Its moves are the moves of $M$, an ε-move from $q_0$ to every start state of $M$,
and an ε-move from every accepting state of $M$ to $q_0$.
