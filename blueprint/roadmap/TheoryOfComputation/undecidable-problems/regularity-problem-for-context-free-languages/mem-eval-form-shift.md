# Shifted right-hand sides denote images of words of $g$

Let $g$ be an encoded context-free
grammar over $T$, let $L_g(n)$ be the language $g$ generates from nonterminal $n$ and $L(g)$ its
language. For a word $u$ over $T$ write $\bar u$ for the same word over $T \sqcup \{\#, 0, 1\}$.
Let $V$ assign to each $m \in \mathbb{N}$ the language $V(m)$ over $T \sqcup \{\#, 0, 1\}$ given by
$V(0) = L(g)\,\#\,\{0,1\}^* \cup T^*\,\#\,\{0^k1^k : k \in \mathbb{N}\}$, $V(1) = \{0,1\}^*$,
$V(2) = T^*$, $V(3) = \{0^k1^k : k \in \mathbb{N}\}$ and $V(n + 4) = \{\bar u : u \in L_g(n)\}$.
Let $\alpha$ be a right-hand side over nonterminals in $\mathbb{N}$ and terminals in $T$, and let
$\alpha'$ be $\alpha$ with each nonterminal $n$ replaced by $n + 4$ and each terminal read in
$T \sqcup \{\#, 0, 1\}$. If $w$ lies in the language that $\alpha'$ denotes when each nonterminal
$m$ is read as $V(m)$, then $w = \bar u$ for some $u$ in the language that $\alpha$ denotes when
each nonterminal $n$ is read as $L_g(n)$.
