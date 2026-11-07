# Context-free languages are exactly the languages of finite pushdown automata

A language
$L$ over an alphabet $T$ is context-free if and only if there are a pushdown automaton $M$ over
$T$ with a finite set of states and a finite stack alphabet, and a finite set $T_0$ of input
letters such that $M$ has no transition, from any state and popping any stack symbol, that
consumes a letter outside $T_0$, for which the language accepted by $M$ by empty stack is $L$.

Here the alphabet, the states and the stack alphabet are types in the lowest universe.
