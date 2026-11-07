# Encoded context-free grammars

An encoded context-free grammar over a terminal type $T$
consists of a start nonterminal, which is a natural number, and a list of productions. Each
production is a pair of a left-hand side, a natural number, and a right-hand side, a list of
elements of the disjoint union $\mathbb{N} \sqcup T$, in which a number $i$ from the left summand
stands for nonterminal $i$ and an element $a$ of $T$ for terminal $a$.

Unlike a general context-free grammar, whose type of nonterminals is part of its data, an
encoded grammar is a concrete object that computable functions can take and return.
