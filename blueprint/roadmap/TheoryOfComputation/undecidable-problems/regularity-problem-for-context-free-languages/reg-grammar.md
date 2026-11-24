# Grammar of the reduction from universality to regularity

Let $g$ be an encoded
context-free grammar over a finite alphabet $T$ with start nonterminal $s$, and write $N_k$ for
nonterminal $k \in \mathbb{N}$ and $\varepsilon$ for the empty word. The reduction grammar of $g$
is the encoded grammar over $T \sqcup \{\#, 0, 1\}$ (the letters of $T$, a separator $\#$ and two
bits $0$ and $1$) with start nonterminal $N_0$ and the productions $N_0 \to N_{s+4}\,\#\,N_1$,
$N_0 \to N_2\,\#\,N_3$, $N_1 \to \varepsilon$, $N_1 \to 0\,N_1$, $N_1 \to 1\,N_1$,
$N_2 \to \varepsilon$, $N_2 \to t\,N_2$ for each $t \in T$, $N_3 \to \varepsilon$ and
$N_3 \to 0\,N_3\,1$, together with the production $N_{n+4} \to \alpha'$ for each production
$N_n \to \alpha$ of $g$, where $\alpha'$ is $\alpha$ with each nonterminal $N_k$ replaced by
$N_{k+4}$ and each letter of $T$ kept.

Its language is $L(g)\,\#\,\{0,1\}^* \cup T^*\,\#\,\{0^n1^n : n \in \mathbb{N}\}$, where $L(g)$
is the language of $g$.
