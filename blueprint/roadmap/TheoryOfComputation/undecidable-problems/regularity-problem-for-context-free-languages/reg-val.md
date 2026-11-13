# Languages assigned to the nonterminals of the regularity grammar

Let $g$ be an encoded
context-free grammar over a finite alphabet $T$ with decidable equality, let $L(g)$ be its
language and $L_g(n)$ the language $g$ generates from nonterminal $n$. Over the alphabet
$T \sqcup \{\#, 0, 1\}$ (the letters of $T$, a separator $\#$ and two bits $0$ and $1$), write
$\bar u$ for a word $u$ over $T$ read in this alphabet. This assigns to each $m \in \mathbb{N}$
the language $V(m)$ over $T \sqcup \{\#, 0, 1\}$ given by
$V(0) = L(g)\,\#\,\{0,1\}^* \cup T^*\,\#\,\{0^k1^k : k \in \mathbb{N}\}$, $V(1) = \{0,1\}^*$,
$V(2) = T^*$, $V(3) = \{0^k1^k : k \in \mathbb{N}\}$ and $V(n + 4) = \{\bar u : u \in L_g(n)\}$.

These are the intended languages of the nonterminals of the regularity grammar of $g$.
