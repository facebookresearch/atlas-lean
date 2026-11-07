# The leftmost derivation along an index sequence

Let
$P = [(t_0, b_0), \dots, (t_{m-1}, b_{m-1})]$ be a list of dominoes, and let $A$, $B$ be the
nonterminals of the ambiguity grammar of $P$ for its top and bottom words. For every nonempty
sequence $i_1, \dots, i_n$ of indices less than $m$ and all words of terminals $u$, $v$, the
canonical rule sequence from $A$ for the words $t_i$ along $i_1, \dots, i_n$ is a leftmost
derivation of $u\, t_{i_1} \cdots t_{i_n}\, i_n \cdots i_1\, v$ from $u\,A\,v$, and the canonical
rule sequence from $B$ for the words $b_i$ along $i_1, \dots, i_n$ is a leftmost derivation of
$u\, b_{i_1} \cdots b_{i_n}\, i_n \cdots i_1\, v$ from $u\,B\,v$.
