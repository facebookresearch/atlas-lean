# The canonical residual map

Let $M$ be an accessible DFA accepting the language $L$. The
residual-language DFA of $L$ has as states the left quotients $x^{-1}L = \{y \mid xy \in L\}$
for words $x$, start state $L$, transitions $K \mapsto a^{-1}K$ on a symbol $a$, and a state $K$
is accepting when it contains the empty word. The canonical residual map is the DFA morphism from
$M$ to this DFA that sends each state $q$ of $M$ to its continuation language, the set of words
$z$ such that running $M$ from $q$ on $z$ ends in an accepting state.
