# Every production of the regularity grammar is sound for its intended languages

Let $g$
be an encoded context-free grammar over a finite alphabet $T$ with decidable equality, and let
$G$ be the regularity grammar of $g$, over the letters of $T$, a separator $\#$ and two bits $0$
and $1$; words over $T$ are read as words over this alphabet. Assign to the nonterminals of $G$
the languages $V(0) = L(g) \# \{0,1\}^* \cup T^* \# \{0^n 1^n : n \ge 0\}$, where $L(g)$ is the
language of $g$, $V(1) = \{0,1\}^*$, $V(2) = T^*$, $V(3) = \{0^n 1^n : n \ge 0\}$, and for each
$n$, $V(n + 4)$ the set of words that $g$ generates from its nonterminal $n$. Then $V$ is a
valuation of $G$: for every production $A \to \alpha$ of $G$, the language obtained from $\alpha$
by replacing each nonterminal $B$ by $V(B)$ and each letter $a$ by $\{a\}$, and concatenating, is
contained in $V(A)$.
