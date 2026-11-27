# The transition monoid recognizes the accepted language

Let $M$ be a DFA with start
state $q_0$ and accepting states $F$. The map sending each word to the element of the transition
monoid of $M$ that it induces recognizes the language accepted by $M$, with accepting set the
elements $f$ of the transition monoid such that $f(q_0) \in F$: a word is accepted by $M$ exactly
when the transformation it induces sends $q_0$ into $F$.
