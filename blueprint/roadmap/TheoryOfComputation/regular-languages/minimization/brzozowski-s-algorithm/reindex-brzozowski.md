# Brzozowski's automaton is the minimal automaton

Let $M$ be a DFA over a finite alphabet
with finitely many states, and let $L$ be its language. For a language $K$ and a word $w$, write
$w^{-1}K = \{v \mid wv \in K\}$ for the left quotient of $K$ by $w$. Every state of Brzozowski's
automaton of $M$ is reached by some word $w$; rename that state to $w^{-1}L$, which does not
depend on the choice of $w$. The renamed automaton is exactly the minimized DFA of $M$: its states
are the left quotients of $L$ by words, its start state is $L$, reading a letter $a$ (a word of
length one) sends $K$ to $a^{-1}K$, and it accepts the $K$ that contain the empty word.
