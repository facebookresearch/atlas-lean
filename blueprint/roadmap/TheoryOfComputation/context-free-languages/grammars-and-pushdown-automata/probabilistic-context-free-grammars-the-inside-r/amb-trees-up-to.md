# Bounded-depth trees of the example grammar

The ambiguous example grammar has one nonterminal $A$, which is its start symbol, one terminal $a$, and the two rules $A \to A\,A$ and $A \to a$. The depth of a leaf is $1$, and the depth of a node is one more than the larger depth of its subtrees. For a natural number $h$, the bounded set of example trees is the finite set of all valid derivation trees of the grammar of depth at most $h$, of any yield. It is obtained by turning each one-nonterminal binary tree of depth at most $h$ into the derivation tree of the same shape.
