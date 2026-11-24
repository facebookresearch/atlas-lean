# Recognizers recognize right quotients

Let $\varphi \colon A^* \to M$ be a monoid
morphism from the free monoid on an alphabet $A$ to a monoid $M$ that recognizes a language $L$
over $A$ through $P \subseteq M$, that is, a word $x$ lies in $L$ exactly when $\varphi(x) \in P$.
Then for every word $u$ over $A$, $\varphi$ recognizes the right quotient $\{x \mid xu \in L\}$
through the set $\{m \in M \mid m\, \varphi(u) \in P\}$.
