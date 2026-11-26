# Recognizers recognize context quotients

Let $\varphi \colon A^* \to M$ be a monoid
morphism from the free monoid on an alphabet $A$ to a monoid $M$ that recognizes a language $L$
over $A$ through $P \subseteq M$, that is, a word $x$ lies in $L$ exactly when $\varphi(x) \in P$.
Then for all words $u, v$ over $A$, $\varphi$ recognizes the context quotient
$\{x \mid uxv \in L\}$ through the set $\{m \in M \mid \varphi(u)\, m\, \varphi(v) \in P\}$.
