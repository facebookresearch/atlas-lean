# States reached in the residual-language DFA

For every language $L$ and every word $x$, the
state that the residual-language DFA of $L$ reaches on reading $x$ is the left quotient
$x^{-1}L = \{z : xz \in L\}$. This automaton has the left quotients of $L$ as states, start state
$L$, transition from $K$ on a letter $a$ to $a^{-1}K$, and accepts $K$ when $K$ contains the empty
word.
