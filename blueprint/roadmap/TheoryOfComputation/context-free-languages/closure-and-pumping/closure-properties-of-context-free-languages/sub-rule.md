# Letter productions of the substitution grammar

Let $g$ be a context-free grammar over
$T$ with nonterminals $N_g$, let $a \in T$ have number $k$ (the position, counted from $0$, of the
first occurrence of $a$ in the list of terminals occurring in the productions of $g$, or the
length of that list when $a$ does not occur in it), and let $n \to w$ be a production over $T'$
whose nonterminals are natural numbers. It gives the production $(k, n) \to w'$ with
nonterminals in $N_g \sqcup (\mathbb{N} \times \mathbb{N})$, where $w'$ keeps the terminals of $w$
and replaces each nonterminal $m$ by $(k, m)$.
