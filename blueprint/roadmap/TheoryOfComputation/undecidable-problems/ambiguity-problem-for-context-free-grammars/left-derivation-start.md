# Leftmost derivations from the start symbol along an index sequence

Let
$P = [(t_0, b_0), \dots, (t_{m-1}, b_{m-1})]$ be a list of dominoes, and let $S$, $A$, $B$ be the
nonterminals of the ambiguity grammar of $P$. For every nonempty sequence $i_1, \dots, i_n$ of
indices less than $m$, the production $S \to A$ followed by the canonical rule sequence from $A$
for the words $t_i$ along $i_1, \dots, i_n$ is a leftmost derivation of
$t_{i_1} \cdots t_{i_n}\, i_n \cdots i_1$ from $S$, and the production $S \to B$ followed by the
canonical rule sequence from $B$ for the words $b_i$ along $i_1, \dots, i_n$ is a leftmost
derivation of $b_{i_1} \cdots b_{i_n}\, i_n \cdots i_1$ from $S$.
