# Substituting the symbols of a grammar

Let $g$ be a context-free grammar over $T$ with
nonterminals $N_g$, and let $e$ assign to each letter $a \in T$ an encoded grammar $e(a)$ over
$T'$. Each symbol of $g$ becomes a nonterminal in $N_g \sqcup (\mathbb{N} \times \mathbb{N})$: a
nonterminal $B$ of $g$ becomes $B$ in the left part, and a terminal $a$ becomes the pair $(k, n)$,
where $k$ is the number of $a$ (the position, counted from $0$, of the first occurrence of $a$ in
the list of terminals occurring in the productions of $g$, or the length of that list when $a$
does not occur in it) and $n$ is the start nonterminal of $e(a)$.
