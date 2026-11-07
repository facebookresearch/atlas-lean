# Nerode classes are the residual languages

Let $L$ be a language over an alphabet
$\Sigma$, and write $x^{-1}L = \{z : xz \in L\}$ for the left quotient of $L$ by a word $x$. This
is the bijection from the classes of the Nerode congruence of $L$ onto the set
$\{x^{-1}L : x \in \Sigma^*\}$ of residual languages of $L$ that sends the class of each word $x$
to $x^{-1}L$.

The residual languages are the states of Mathlib's residual-language DFA of $L$.
