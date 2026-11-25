# Charged decoding of encoded grammar symbols

Let $T$ be an alphabet. An encoded context-free grammar over an alphabet $T$ consists of a start nonterminal $n_0 \in \mathbb{N}$ and a finite list of encoded productions $(A, \gamma)$ with $A \in \mathbb{N}$ and $\gamma$ a finite word over the disjoint union of $\mathbb{N}$ (nonterminals) and $T$ (terminals); decoding a symbol reads an element of $\mathbb{N}$ as a nonterminal and an element of $T$ as a terminal, and decoding a production $(A, \gamma)$ gives the production $A \to \gamma'$ with $\gamma'$ the symbolwise decoding of $\gamma$. A costed computation returns a value together with a cost in $\mathbb{N}$. The costed decoding of a list of encoded symbols is defined by recursion: the empty
list gives the empty list at cost $1$; a list $s, s_2, \dots, s_k$ gives the decoding of $s$ followed by the value
for $s_2, \dots, s_k$, at that cost plus $4$.
