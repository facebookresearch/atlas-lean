# The Nerode automaton is the residual-language automaton

Let $L$ be a language over an
alphabet $\Sigma$, and write $x^{-1}L = \{z : xz \in L\}$ for the left quotient of $L$ by a word
$x$. Consider the canonical automaton of $L$ as a DFA: its states are the classes $[x]$ of the
Nerode congruence of $L$, its start state is the class of the empty word, on a letter $a$ it goes
from $[x]$ to $[xa]$, and its accepting states are the classes of words of $L$. Renaming each
class $[x]$ to $x^{-1}L$ gives exactly Mathlib's residual-language DFA of $L$: its states are the
residual languages $x^{-1}L$ for $x \in \Sigma^*$, its start state is $L$, on a letter $a$ it goes
from $K$ to $a^{-1}K$, and its accepting states are the residual languages that contain the empty
word.
