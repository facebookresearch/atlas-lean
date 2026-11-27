# Productions of the regularity grammar preserve generated languages

Let $g$ be an
encoded context-free grammar over a finite alphabet $T$ with decidable equality, let $G$ be the
regularity grammar of $g$, over the letters of $T$, a separator $\#$ and two bits $0$ and $1$,
and for a nonterminal $B$ let $L_G(B)$ be the language that the grammar denoted by $G$ generates
from $B$. If $(A, \alpha)$ is an encoded production of $G$ and $w$ is a word in the language that
the decoded right-hand side $\alpha$ denotes when each nonterminal $B$ is read as $L_G(B)$, each
letter $a$ as $\{a\}$, and these languages are concatenated in order, then $w \in L_G(A)$.
