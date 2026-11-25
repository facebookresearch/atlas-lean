# Finite pushdown automata accept context-free languages

Let $M$ be a pushdown automaton
with a finite set of states and a finite stack alphabet, and suppose that there is a finite set
$T_0$ of input letters such that $M$ has no transition, from any state and popping any stack
symbol, that consumes a letter outside $T_0$. Then the language accepted by $M$ by empty stack
is context-free.
