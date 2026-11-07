# Leftmost derivations from $A$ and $B$ follow an index sequence

Let
$P = [(t_0, b_0), \dots, (t_{m-1}, b_{m-1})]$ be a list of dominoes, let $A$, $B$ be the
nonterminals of the ambiguity grammar of $P$ for its top and bottom words, and let $u$, $v$ be
words of terminals. Every leftmost derivation of a word $w$ from the sentential form $u\,A\,v$ is
the canonical rule sequence from $A$ for the words $t_i$ along some nonempty sequence
$i_1, \dots, i_n$ of indices less than $m$, and
$w = u\, t_{i_1} \cdots t_{i_n}\, i_n \cdots i_1\, v$. Likewise, every leftmost derivation of $w$
from $u\,B\,v$ is the canonical rule sequence from $B$ for the words $b_i$ along such a sequence,
and $w = u\, b_{i_1} \cdots b_{i_n}\, i_n \cdots i_1\, v$.
