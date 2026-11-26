# Shape of an example derivation tree

The ambiguous example grammar has one nonterminal $A$, which is its start symbol, one terminal $a$, and the two rules $A \to A\,A$ and $A \to a$. The shape of a derivation tree of this grammar is the one-nonterminal binary tree obtained recursively: a leaf becomes a leaf, and a node becomes a node whose subtrees are the shapes of its subtrees; the labels are forgotten.
