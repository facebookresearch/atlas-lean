# Main production of the substitution grammar

Let $g$ be a context-free grammar over $T$
with nonterminals $N_g$, and let $e$ assign to each letter $a \in T$ an encoded grammar $e(a)$
over $T'$. A production $A \to \alpha$ over $T$ with nonterminals in $N_g$ gives the production
$A \to \alpha'$ over $T'$ with nonterminals in $N_g \sqcup (\mathbb{N} \times \mathbb{N})$, where
$A$ is taken in the left part and $\alpha'$ is obtained from $\alpha$ by replacing each
nonterminal $B$ by $B$ in the left part and each terminal $a$ by the nonterminal $(k, n)$; here
$k$ is the number of $a$ (the position, counted from $0$, of the first occurrence of $a$ in the
list of terminals occurring in the productions of $g$, or the length of that list when $a$ does
not occur in it) and $n$ is the start nonterminal of $e(a)$.
