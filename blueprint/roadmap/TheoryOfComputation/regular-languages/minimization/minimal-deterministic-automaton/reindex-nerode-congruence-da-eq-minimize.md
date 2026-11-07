# The canonical automaton of a DFA's language is its minimized DFA

Let $M$ be a DFA over
an alphabet $\Sigma$ accepting the language $L$, and write $x^{-1}L = \{z : xz \in L\}$ for the
left quotient of $L$ by a word $x$. Consider the canonical automaton of $L$ as a DFA: its states
are the classes $[x]$ of the Nerode congruence of $L$, its start state is the class of the empty
word, on a letter $a$ it goes from $[x]$ to $[xa]$, and its accepting states are the classes of
words of $L$. Renaming each class $[x]$ to $x^{-1}L$, regarded as one of the languages accepted
from the states of $M$ reachable from its start state, gives exactly the minimized DFA of $M$.
