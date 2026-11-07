# Leftmost derivations in the ambiguity grammar

Let
$P = [(t_0, b_0), \dots, (t_{m-1}, b_{m-1})]$ be a list of dominoes, and let $S$, $A$, $B$ be the
nonterminals of the ambiguity grammar of $P$. Every leftmost derivation of a word $w$ from $S$ in
that grammar has one of two forms, for some nonempty sequence $i_1, \dots, i_n$ of indices less
than $m$: either it is $S \to A$ followed by the canonical rule sequence from $A$ for the words
$t_i$ along $i_1, \dots, i_n$, and $w = t_{i_1} \cdots t_{i_n}\, i_n \cdots i_1$; or it is
$S \to B$ followed by the canonical rule sequence from $B$ for the words $b_i$ along
$i_1, \dots, i_n$, and $w = b_{i_1} \cdots b_{i_n}\, i_n \cdots i_1$.
