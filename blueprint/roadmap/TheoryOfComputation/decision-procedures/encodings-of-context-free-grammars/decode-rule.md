# Decoding a production

Decoding a pair $(A, s)$ of a natural number $A$ and a list $s$
of elements of the disjoint union $\mathbb{N} \sqcup T$ gives the production, with terminals
$T$ and nonterminals $\mathbb{N}$, whose left-hand side is the nonterminal $A$ and whose
right-hand side is $s$ with each entry decoded as a symbol: a number $i$ from the left summand
becomes the nonterminal $i$ and an element $a$ of $T$ becomes the terminal $a$.
