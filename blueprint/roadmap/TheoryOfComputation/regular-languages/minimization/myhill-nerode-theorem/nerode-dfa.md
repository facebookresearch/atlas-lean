# The Nerode automaton

Let $L$ be a language over an alphabet $\Sigma$. The Nerode
automaton of $L$ is the deterministic automaton over $\Sigma$, not necessarily finite, whose
states are the Nerode classes of words for $L$, whose start state is the class of the empty
word, which on reading a symbol $a \in \Sigma$ moves from the class of a word $x$ to the class
of $xa$, and whose accepting states are the classes of the words in $L$.
